//! Coordinator-owned session planning (M4.1).
//!
//! This module is the first slice of the M4 session-ownership migration. It
//! moves the mailbox, the tree plan engine, read admission/backlog, pending
//! network tracking, persistence intent, timeout budget, and cancellation into
//! one [`SessionPlan`] owned by the coordinator. No component other than the
//! coordinator may own these session lifecycle states.
//!
//! Ownership rules enforced here:
//!
//! * The [`SessionPlan`] owns the bounded mailbox (`128` packets / `4 MiB` by
//!   default, carried from the admission budget) and clears it on cancellation.
//! * Every dispatched read carries an [`OperationRef`]; a read completion may
//!   mutate the plan only when it matches the exact in-flight operation
//!   (`pending_reads` is keyed by hash and matched by full operation identity).
//! * A tree engine is uniquely owned by the plan while it advances; events
//!   queue in the mailbox until a rooted plan exists (`PlanSeed`).
//! * Persistence intent is a single state machine: `Persist` -> `WritePending`
//!   -> `FencePending` -> `Durable`. A write batch carries its fence operation
//!   so one adapter barrier reports both `WriteCompleted` and
//!   `DurabilityFenced`.
//! * The tree engine is never advanced by two threads: `run_turn` runs bounded
//!   CPU turns on the coordinator owner task only.
//!
//! The [`TreeEngine`] port is the only place shamap tree types cross the crate
//! boundary. Adapters (the app wiring in M4.2) implement it; higher-level
//! coordinator types stay shamap-free.

use bytes::Bytes;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;

use basics::base_uint::Uint256;
use basics::intrusive_pointer::SharedIntrusive;
use basics::random::rand_int_to;
use basics::sha_map_hash::SHAMapHash;
use ledger::{
    InboundLedgerDataType, InboundLedgerNodeData, InboundLedgerPacket, InboundLedgerPeerScore,
    Ledger, TreeAdvance, TreeKind, TreePlan, TreePlanId, select_inbound_ledger_reply_peers,
};
use shamap::node_id::{SHAMapNodeId, deserialize_shamap_node_id};
use shamap::sync::{MissingNodeReadApply, MissingNodeReadOutcome, MissingNodeResidentLookup};
use shamap::tree_node::SHAMapTreeNode;

use crate::id::{IdCounter, PeerId, StoreGeneration};
use crate::identity::{OperationKind, OperationRef, SessionRef};
use crate::ingress::{AdmissionBudget, AdmittedLedgerPacket};
use crate::io::{
    DurabilityOutcome, PersistNode, ReadCompletion, ReadOutcome, ReadPriority, ReadRequest,
    WriteBatch, WriteOutcome,
};
use crate::session::{CancelReason, FailureReason};

/// One deferred NodeStore round, matching rippled's `MissingNodes` maxDefer
/// of 512. The separate missing-node network output maximum remains 256.
pub const MAX_NEW_READS_PER_PASS: usize = 512;
/// Bounded tree turns per event; a plan must return to the coordinator owner
/// between turns so control events are never starved.
pub const MAX_TURNS_PER_EVENT: u32 = 4;
/// Bounded packet feed per turn; remaining packets stay in the mailbox.
pub const MAX_PACKETS_FED_PER_TURN: usize = 4;
/// Unique pending reads cap (mirrors the broker logical admission ceiling).
pub const MAX_PENDING_READS: usize = 512;
/// Aggregate exact frontier across rippled's six useful reply peers. Each
/// reply-triggered scan may send 128 distinct node IDs, so the coordinator
/// retains six independent lanes rather than treating the per-scan 256 search
/// bound as a global outstanding ceiling.
pub const MAX_RETAINED_NETWORK_FRONTIER: usize = 6 * 128;
/// Maximum exact frontier nodes retried during one no-progress timeout. This
/// matches rippled's blind request cap (`kReqNodes`) while a rotating cursor
/// gives every retained frontier entry a bounded chance to be retried.
pub const MAX_TIMEOUT_REPROBES: usize = 12;
/// No-progress recovery intervals permitted before the following seventh
/// no-progress interval fails the acquisition (mirrors rippled
/// `kLedgerTimeoutRetriesMax`).
pub const DEFAULT_MAX_ACQUIRE_TIMEOUTS: u32 = 6;

/// One unique missing node a tree engine discovered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlanReadNeed {
    hash: SHAMapHash,
    ledger_seq: u32,
    node_id: SHAMapNodeId,
    branch: usize,
}

impl PlanReadNeed {
    /// Builds a read need.
    pub const fn new(
        hash: SHAMapHash,
        ledger_seq: u32,
        node_id: SHAMapNodeId,
        branch: usize,
    ) -> Self {
        Self {
            hash,
            ledger_seq,
            node_id,
            branch,
        }
    }

    /// The node key to read.
    pub const fn hash(&self) -> SHAMapHash {
        self.hash
    }

    /// The ledger sequence scope of the read.
    pub const fn ledger_seq(&self) -> u32 {
        self.ledger_seq
    }

    /// The node identity within the tree.
    pub const fn node_id(&self) -> SHAMapNodeId {
        self.node_id
    }

    /// The parent branch the node attaches to.
    pub const fn branch(&self) -> usize {
        self.branch
    }
}

/// One missing tree node that must be requested from a peer. The tree kind is
/// part of the request identity: a state-node hash must never be emitted as a
/// transaction-node request (or vice versa).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PlanNetworkNeed {
    node_id: SHAMapNodeId,
    hash: Uint256,
    kind: TreeKind,
}

impl PlanNetworkNeed {
    /// Builds a kind-qualified network need.
    pub const fn new(node_id: SHAMapNodeId, hash: Uint256, kind: TreeKind) -> Self {
        Self {
            node_id,
            hash,
            kind,
        }
    }

    /// The missing node's tree location.
    pub const fn node_id(self) -> SHAMapNodeId {
        self.node_id
    }

    /// The requested node hash.
    pub const fn hash(self) -> Uint256 {
        self.hash
    }

    /// The SHAMap tree that owns this node.
    pub const fn kind(self) -> TreeKind {
        self.kind
    }
}

/// Result of one bounded engine turn. Maps the shamap/ledger
/// `TreeAdvance` vocabulary without leaking it into the coordinator surface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanStepOutcome {
    /// No work command in this turn; the engine may still be runnable.
    Ready,
    /// Unique missing nodes to submit to the NodeStore broker.
    NeedsReads(Vec<PlanReadNeed>),
    /// Unique network candidates to request from a peer.
    NeedsNetwork(Vec<PlanNetworkNeed>),
    /// The tree is structurally complete; the session must persist and fence.
    Complete,
    /// The tree plan is invalid for this session.
    Invalid,
}

/// Result of applying exactly one read/network completion to an engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlanReadApply {
    /// The node attached; `attached_edges` edges were resolved and
    /// `missing_edges` remain pending.
    Applied {
        /// Resolved descendant edges.
        attached_edges: usize,
        /// Still-missing descendant edges.
        missing_edges: usize,
    },
    /// Admission was not available; the need remains eligible for a FIFO retry.
    Requeued,
    /// The read was explicitly cancelled.
    Cancelled,
    /// The plan id does not match the current traversal.
    StalePlan,
    /// The node did not match its expected hash.
    HashMismatch,
    /// The read was never dispatched by this plan.
    UnknownRead,
}

/// Result of routing one peer-supplied node through the ledger map and the
/// retained traversal. `useful` is deliberately separate from `attachment`:
/// rippled resets an inbound ledger timeout only when `SHAMapAddNode` credits
/// useful data, while the retained traversal may still need a duplicate node
/// to wake a previously announced frontier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PlanNetworkApply {
    attachment: PlanReadApply,
    useful: bool,
    invalid: bool,
}

impl PlanNetworkApply {
    /// Builds an application result from the retained-frontier outcome and the
    /// map-level useful-data accounting.
    pub const fn new(attachment: PlanReadApply, useful: bool) -> Self {
        Self {
            attachment,
            useful,
            invalid: false,
        }
    }

    /// Reports a packet-fatal node validation failure. rippled aborts the
    /// remainder of the packet on the first invalid node/data/id tuple.
    pub const fn invalid(attachment: PlanReadApply, useful: bool) -> Self {
        Self {
            attachment,
            useful,
            invalid: true,
        }
    }

    /// The retained-frontier attachment outcome.
    pub const fn attachment(self) -> PlanReadApply {
        self.attachment
    }

    /// True only when the ledger map accepted useful peer data.
    pub const fn is_useful(self) -> bool {
        self.useful
    }

    /// True when the retained continuation attached at least one edge.
    pub const fn attached(self) -> bool {
        matches!(self.attachment, PlanReadApply::Applied { .. })
    }

    /// True when later nodes from the same packet must not be processed.
    pub const fn is_invalid(self) -> bool {
        self.invalid
    }
}

/// The uniquely owned tree engine of one session plan. This is the only place
/// shamap tree types cross into the crate; adapters implement it, the
/// coordinator owns it, and it is never advanced concurrently.
pub trait TreeEngine: std::fmt::Debug {
    /// The traversal identity of this engine.
    fn plan_id(&self) -> TreePlanId;

    /// One bounded CPU turn. `max_new_reads` caps newly announced reads.
    fn advance(&mut self, max_new_reads: usize) -> PlanStepOutcome;

    /// Applies one broker read completion. `outcome` carries decoded bytes;
    /// the engine deserializes and attaches the node.
    fn apply_read(&mut self, hash: SHAMapHash, outcome: &ReadOutcome) -> PlanReadApply;

    /// Applies one asynchronous timeout reprobe to the exact retained network
    /// need that dispatched it. Storage bytes are prefix-form NodeStore data,
    /// never wire ledger-data bytes. The exact need prevents a late reprobe
    /// from attaching a different location that merely shares a hash.
    fn apply_recovery_read(
        &mut self,
        need: PlanNetworkNeed,
        outcome: &ReadOutcome,
    ) -> PlanReadApply;

    /// Applies one decoded network node to the retained frontier. `kind`
    /// distinguishes state from transaction nodes so an app engine can route
    /// each node to its ledger map; `node` carries the raw wire bytes and
    /// node-id that the engine deserializes and attaches.
    fn apply_network_node(
        &mut self,
        kind: TreeKind,
        node: &InboundLedgerNodeData,
    ) -> PlanNetworkApply;

    /// Starts a fresh reply-triggered missing-node scan epoch after useful
    /// peer data, matching rippled's per-Reply `getMissingNodes(256)` call.
    fn begin_reply_scan(&mut self) {}

    /// Retains canonical peer-attachment waiters only for exact needs that
    /// were actually serialized, discarding a truncated scan tail.
    fn retain_network_needs(&mut self, _needs: &[PlanNetworkNeed]) {}

    /// Re-announce retained SHAMap read waiters after actor operation
    /// identities are invalidated without dropping the owned tree graph.
    fn rearm_pending_reads(&mut self) {}

    /// True only while a CPU turn can make progress without a broker completion
    /// or peer response.
    fn has_runnable_frontier(&self) -> bool;

    /// Total branch selections consumed by the retained traversal.
    fn branch_steps(&self) -> u64;

    /// The verified header sequence available as soon as a Base packet seeds
    /// the engine. Node requests use it to scope TMGetObjectByHash even when
    /// the acquisition began by hash with no initial sequence.
    fn ledger_sequence(&self) -> Option<u32> {
        None
    }

    /// Drains accepted NodeStore writes accumulated since the prior call.
    /// Nodes are written incrementally while acquisition continues; only the
    /// final batch is followed by a durability fence and durable handoff.
    fn take_persistable_nodes(&mut self) -> Vec<PersistNode>;

    /// Reports that the exact NodeStore write batch containing the engine's
    /// previously drained accepted nodes was accepted. Engines may now publish
    /// shared completion metadata; the default is a no-op for pure/test plans.
    fn on_persistence_accepted(&mut self) {}

    /// The verified ledger-header sequence that scopes persistence. A missing
    /// value makes completion invalid: NodeStore records must never use an
    /// inferred or placeholder sequence.
    fn persistence_sequence(&self) -> Option<u32>;

    /// Yields the fully materialized ledger exactly once, after the durability
    /// fence passed and the tree is structurally complete. The coordinator's
    /// durable handoff consumes this; subsequent calls return `None`.
    fn durable_ledger(&mut self) -> Option<Arc<Ledger>>;
}

/// One-shot construction of a rooted [`TreeEngine`] from the first Base/header
/// packet of a session. `None` means no rooted plan yet; packets queue in the
/// session mailbox until a later header packet succeeds.
///
/// This is a construction port: it runs outside coordinator state mutation and
/// returns a uniquely owned engine or nothing. It never exposes a mutable
/// session.
pub trait PlanSeed: std::fmt::Debug {
    /// Attempts the pre-peer local reconstruction path. Implementations must
    /// use resident/cache data only; physical I/O remains brokered.
    fn build_resident(
        &mut self,
        _session: SessionRef,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        None
    }

    /// Builds from prefixed Ledger NodeStore bytes returned by the brokered
    /// pre-peer header probe.
    fn build_stored_header(
        &mut self,
        _session: SessionRef,
        _data: &Bytes,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        None
    }

    /// Releases constructor metadata after the coordinator's terminal
    /// one-minute retention expires.
    fn session_reaped(&mut self, _session: SessionRef) {}

    /// Builds a rooted tree engine for `session` from `header`, or `None`.
    fn build(
        &mut self,
        session: SessionRef,
        header: &InboundLedgerPacket,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>>;
}

/// The default plan seed: never builds an engine, so packets stay in the
/// mailbox and the session waits for the app adapter to supply a seed.
#[derive(Debug, Clone, Copy, Default)]
pub struct NullPlanSeed;

impl PlanSeed for NullPlanSeed {
    fn build(
        &mut self,
        _session: SessionRef,
        _header: &InboundLedgerPacket,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        None
    }
}

/// A resident lookup that never resolves: no synchronous NodeStore or network
/// I/O is ever introduced into traversal.
#[derive(Debug, Clone, Copy, Default)]
pub struct NullResident;

impl MissingNodeResidentLookup for NullResident {
    fn load_resident(
        &mut self,
        _hash: SHAMapHash,
        _ledger_seq: u32,
    ) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        None
    }
}

/// Bounded, coordinator-owned packet mailbox for one session.
///
/// Admission leases reserve capacity before a decoded packet is routed; the
/// mailbox enforces the same bounds defensively so a misconfigured or replaying
/// ingress cannot overflow coordinator state. Counters track *currently queued*
/// packets and bytes.
#[derive(Debug)]
pub struct SessionMailbox {
    packets: VecDeque<AdmittedLedgerPacket>,
    packet_count: u64,
    packet_bytes: u64,
    max_packets: u64,
    max_bytes: u64,
}

impl SessionMailbox {
    /// Builds a mailbox with explicit packet/byte bounds.
    pub const fn new(max_packets: u64, max_bytes: u64) -> Self {
        Self {
            packets: VecDeque::new(),
            packet_count: 0,
            packet_bytes: 0,
            max_packets,
            max_bytes,
        }
    }

    /// Accepts a packet if it fits the remaining packet/byte budget. Returns
    /// false (and mutates nothing) when the budget is exhausted.
    pub fn push(&mut self, packet: AdmittedLedgerPacket) -> bool {
        let packets = packet.lease().packet_count();
        let bytes = packet.lease().byte_count();
        if self.packet_count.saturating_add(packets) > self.max_packets
            || self.packet_bytes.saturating_add(bytes) > self.max_bytes
        {
            return false;
        }
        self.packet_count += packets;
        self.packet_bytes += bytes;
        self.packets.push_back(packet);
        true
    }

    /// Removes the oldest queued packet and returns it, restoring its reserved
    /// counts.
    pub fn pop_front(&mut self) -> Option<AdmittedLedgerPacket> {
        let packet = self.packets.pop_front()?;
        self.packet_count = self
            .packet_count
            .saturating_sub(packet.lease().packet_count());
        self.packet_bytes = self
            .packet_bytes
            .saturating_sub(packet.lease().byte_count());
        Some(packet)
    }

    /// Currently queued packet count.
    pub fn packet_count(&self) -> u64 {
        self.packet_count
    }

    /// Currently queued packet bytes.
    pub fn packet_bytes(&self) -> u64 {
        self.packet_bytes
    }

    /// Number of queued packets.
    pub fn len(&self) -> usize {
        self.packets.len()
    }

    /// True when no packets are queued.
    pub fn is_empty(&self) -> bool {
        self.packets.is_empty()
    }

    /// Drops all queued packets and restores the reserved counts.
    pub fn clear(&mut self) {
        self.packets.clear();
        self.packet_count = 0;
        self.packet_bytes = 0;
    }
}

/// Persistence intent of one session: the single write/fence state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SessionPersistence {
    /// Nothing to persist yet.
    None,
    /// An accepted-node batch was dispatched while acquisition continues.
    /// It has no durability fence and must settle before another plan turn.
    IncrementalWritePending {
        /// The dispatched write operation.
        operation: OperationRef,
    },
    /// The final write batch was dispatched; `operation` is its write identity
    /// and `fence` is the durability-barrier operation the adapter will report.
    FinalWritePending {
        /// The dispatched write operation.
        operation: OperationRef,
        /// The fence operation to match the later durability completion.
        fence: OperationRef,
    },
    /// The write was accepted; the durability fence is in flight.
    FencePending {
        /// The in-flight fence operation.
        operation: OperationRef,
    },
    /// The ordered NodeStore acceptance fence passed; the reconstructible
    /// ledger is safe to hand off. This does not imply a per-ledger fsync.
    Durable,
    /// Persistence or the fence failed; no normal adoptable ledger exists.
    Failed {
        /// Why persistence failed.
        reason: FailureReason,
    },
}

impl SessionPersistence {
    /// A stable label for tracing.
    pub const fn label(&self) -> &'static str {
        match self {
            Self::None => "none",
            Self::IncrementalWritePending { .. } => "incremental_write_pending",
            Self::FinalWritePending { .. } => "final_write_pending",
            Self::FencePending { .. } => "fence_pending",
            Self::Durable => "durable",
            Self::Failed { .. } => "failed",
        }
    }
}

/// The outcome of a read completion applied to the plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlanReadOutcome {
    /// The completion matched an in-flight read and was applied.
    Applied,
    /// No in-flight read matches the operation; the completion is stale.
    Stale,
}

/// The outcome of a write completion applied to the plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlanWriteOutcome {
    /// The accepted-node write completed; planning may resume.
    IncrementalAccepted,
    /// The final write completed and its durability fence is now in flight.
    FinalAccepted,
    /// The write failed; the session must terminalize.
    Failed(FailureReason),
    /// The exact write was cancelled because its NodeStore generation is no
    /// longer valid; the session must be cancelled rather than left pending.
    Cancelled(CancelReason),
    /// No in-flight write matches the operation; stale.
    Stale,
}

/// The outcome of a durability-fence completion applied to the plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlanDurabilityOutcome {
    /// The exact in-flight fence passed; the ledger is durable.
    Durable,
    /// The fence failed; the session must terminalize.
    Failed(FailureReason),
    /// No in-flight fence matches the operation; stale.
    Stale,
}

/// The outcome of a deadline timeout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlanTimeout {
    /// Another retry may proceed.
    Continue,
    /// The retry budget is exhausted; the session must fail.
    Fail,
}

/// Context handed to the plan so it can mint exact operation identities without
/// reaching into the coordinator.
pub struct TurnContext<'a> {
    /// The session being planned.
    pub session: SessionRef,
    /// The NodeStore generation to scope reads/writes.
    pub store_generation: StoreGeneration,
    /// Read admission priority derived from the acquisition reason.
    pub priority: ReadPriority,
    /// The coordinator id counter (the only source of operation ids).
    pub ids: &'a mut IdCounter,
}

/// One bounded work command produced by a plan turn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanTurn {
    /// No work; wait for another event.
    Continue,
    /// Submit these brokered reads.
    Reads(Vec<ReadRequest>),
    /// Request these hashes from a peer.
    Network(Vec<PlanNetworkNeed>),
    /// Persist this batch; the batch carries its fence operation.
    Persist(WriteBatch),
    /// The plan is invalid; the session must fail.
    Invalid,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NetworkLane {
    Reply(PeerId),
    Added(PeerId),
    Timeout(Vec<PeerId>),
}

/// Packet-level application summary. Attachment controls whether another
/// bounded CPU turn is useful; useful data alone controls timeout progress.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct PacketFeed {
    attached: bool,
    useful: bool,
    nodes_seen: u32,
    malformed_nodes: u32,
    useful_peer_counts: BTreeMap<PeerId, i32>,
    /// Exact retained needs attached by this packet. These are the only
    /// network results allowed to retire retained needs.
    resolved_network: Vec<PlanNetworkNeed>,
}

impl PacketFeed {
    fn merge(&mut self, mut other: Self) {
        self.attached |= other.attached;
        self.useful |= other.useful;
        self.nodes_seen = self.nodes_seen.saturating_add(other.nodes_seen);
        self.malformed_nodes = self.malformed_nodes.saturating_add(other.malformed_nodes);
        for (peer, count) in other.useful_peer_counts {
            self.useful_peer_counts
                .entry(peer)
                .and_modify(|current| *current = (*current).max(count))
                .or_insert(count);
        }
        self.resolved_network.append(&mut other.resolved_network);
    }
}

/// The coordinator-owned plan of one session (M4.1).
///
/// Owns the mailbox, the uniquely owned [`TreeEngine`], read admission and
/// backlog, pending network tracking, the persistence state machine, the
/// timeout budget, and cancellation. The runner calls [`Self::run_turn`] with a
/// [`TurnContext`]; reads/writes/fences/timers are applied through the typed
/// `on_*` methods, each validating the exact operation identity.
#[derive(Debug)]
pub struct SessionPlan {
    engine: Option<Box<dyn TreeEngine + Send + Sync>>,
    mailbox: SessionMailbox,
    pending_reads: BTreeMap<SHAMapHash, OperationRef>,
    /// Exact timeout reprobes are intentionally separate from ordinary
    /// traversal reads: the original read may already have settled while its
    /// retained network need remains recoverable.
    pending_recovery_reads: BTreeMap<OperationRef, PlanNetworkNeed>,
    read_backlog: VecDeque<PlanReadNeed>,
    /// Exact frontier work waiting for a retained-dispatch slot. This holds at
    /// most one engine-announced bounded batch because `run_turn` does not
    /// advance the engine while it is nonempty.
    network_backlog: VecDeque<PlanNetworkNeed>,
    /// Hash view of the exact current frontier: both dispatched retained work
    /// and work waiting in `network_backlog`. It is rebuilt on every exact
    /// retirement, so it never reports historical requests as pending.
    pending_network: BTreeSet<Uint256>,
    /// Exact currently dispatched network frontier. Timeout recovery retains
    /// node id, hash, and tree kind so it can resend a protocol-correct
    /// request; overflow remains in `network_backlog` until capacity frees.
    retained_network: Vec<PlanNetworkNeed>,
    /// Exact retained needs that have not yet been serialized into a normal
    /// peer request. Entries move here exactly once when they enter
    /// `retained_network`; normal owner events remove one bounded FIFO batch,
    /// while timeout recovery continues to use `retained_network` directly.
    unemitted_network: VecDeque<PlanNetworkNeed>,
    /// Start index for the next bounded timeout recovery batch. It advances
    /// once per timeout interval, not once per effect, so local reprobes and
    /// peer resends cover the same exact needs.
    retained_network_cursor: usize,
    useful_peer_scores: BTreeMap<PeerId, i32>,
    network_lanes: VecDeque<NetworkLane>,
    recent_nodes: BTreeSet<Uint256>,
    persistence: SessionPersistence,
    timeouts: u32,
    progress_since_timeout: bool,
    max_timeouts: u32,
    pending_reads_cap: usize,
    cancelled: bool,
    runs: u64,
}

impl SessionPlan {
    /// Builds a plan with an admission budget (packet/byte mailbox limits).
    pub fn new(admission: AdmissionBudget) -> Self {
        Self {
            engine: None,
            mailbox: SessionMailbox::new(admission.max_packets(), admission.max_bytes()),
            pending_reads: BTreeMap::new(),
            pending_recovery_reads: BTreeMap::new(),
            read_backlog: VecDeque::new(),
            network_backlog: VecDeque::new(),
            pending_network: BTreeSet::new(),
            retained_network: Vec::new(),
            unemitted_network: VecDeque::new(),
            retained_network_cursor: 0,
            useful_peer_scores: BTreeMap::new(),
            network_lanes: VecDeque::new(),
            recent_nodes: BTreeSet::new(),
            persistence: SessionPersistence::None,
            timeouts: 0,
            progress_since_timeout: false,
            max_timeouts: DEFAULT_MAX_ACQUIRE_TIMEOUTS,
            pending_reads_cap: MAX_PENDING_READS,
            cancelled: false,
            runs: 0,
        }
    }

    /// Builds a plan with explicit timeout retries (tests).
    pub fn with_max_timeouts(admission: AdmissionBudget, max_timeouts: u32) -> Self {
        Self {
            max_timeouts,
            ..Self::new(admission)
        }
    }

    /// Builds a plan with a smaller pending-read cap (tests).
    pub fn with_pending_reads_cap(admission: AdmissionBudget, pending_reads_cap: usize) -> Self {
        Self {
            pending_reads_cap,
            ..Self::new(admission)
        }
    }

    /// The uniquely owned tree engine, if a rooted plan exists yet.
    pub fn engine(&self) -> Option<&(dyn TreeEngine + Send + Sync)> {
        self.engine.as_deref()
    }

    pub fn has_runnable_frontier(&self) -> bool {
        self.engine
            .as_deref()
            .is_some_and(TreeEngine::has_runnable_frontier)
    }

    /// The verified header sequence available for subsequent by-hash node
    /// requests. It deliberately does not depend on tree completion.
    pub fn ledger_sequence(&self) -> Option<u32> {
        self.engine
            .as_deref()
            .and_then(TreeEngine::ledger_sequence)
            .filter(|sequence| *sequence != 0)
    }

    pub fn network_lane(&self) -> Option<NetworkLane> {
        self.network_lanes.front().cloned()
    }

    pub fn network_lane_exhausted(&self) -> bool {
        self.network_lanes.front().is_some()
            && self.unemitted_network.is_empty()
            && self.network_backlog.is_empty()
            && self.pending_read_count() == 0
            && !self.has_runnable_frontier()
    }

    pub fn finish_network_lane(&mut self) {
        if self.network_lanes.pop_front().is_some() {
            self.discard_unrequested_network_tail();
        }
        // Each queued useful peer gets an independent getMissingNodes-style
        // scan. After the final lane, however, rippled waits for a peer/timer
        // trigger; it does not create another scan merely because the prior
        // request was serialized. Leaving the exhausted result dormant also
        // prevents unrelated write or stale-packet wakes from churning a fresh
        // root walk with no peer lane to receive its output.
        if !self.network_lanes.is_empty()
            && let Some(engine) = self.engine.as_mut()
        {
            engine.begin_reply_scan();
        }
    }

    fn discard_unrequested_network_tail(&mut self) {
        let unrequested = self
            .unemitted_network
            .iter()
            .chain(self.network_backlog.iter())
            .copied()
            .collect::<Vec<_>>();
        self.retained_network
            .retain(|need| !unrequested.contains(need));
        self.unemitted_network.clear();
        self.network_backlog.clear();
        self.normalize_retained_network_cursor();
        self.refresh_pending_network();
        if let Some(engine) = self.engine.as_mut() {
            engine.retain_network_needs(&self.retained_network);
        }
    }

    /// Credits a verified Base/header reply to its responder. The header is
    /// useful acquisition data in rippled and therefore receives Reply
    /// trigger semantics after any asynchronous local reads finish.
    pub fn note_useful_peer(&mut self, peer: PeerId, count: i32) {
        self.useful_peer_scores
            .entry(peer)
            .and_modify(|current| *current = (*current).max(count))
            .or_insert(count);
    }

    pub fn begin_timeout_scan(
        &mut self,
        existing_peers: Vec<PeerId>,
        added_peers: impl IntoIterator<Item = PeerId>,
    ) {
        self.recent_nodes.clear();
        let was_empty = self.network_lanes.is_empty();
        self.network_lanes
            .push_back(NetworkLane::Timeout(existing_peers));
        self.network_lanes
            .extend(added_peers.into_iter().map(NetworkLane::Added));
        if was_empty {
            // Keep any actor-visible exact frontier while rebuilding the
            // SHAMap view. A useful partial reply may have cleared that
            // frontier while `recent_nodes` suppressed the unanswered
            // candidates produced by the reply scan. rippled's Timeout
            // trigger clears `recentNodes_` and calls `getMissingNodes` again;
            // restarting the engine scan here makes those retained SHAMap
            // edges visible again without duplicating an extant actor need.
            if !self.network_lanes.is_empty()
                && let Some(engine) = self.engine.as_mut()
            {
                engine.begin_reply_scan();
            }
        }
    }

    /// Mirrors `InboundLedger::onTimer`: recent request suppression is scoped
    /// to one timer interval and is cleared even when that interval made
    /// progress. A progress interval does not restart the active traversal.
    pub fn clear_recent_nodes(&mut self) {
        self.recent_nodes.clear();
    }

    fn reset_network_epoch(&mut self) {
        self.network_backlog.clear();
        self.pending_network.clear();
        self.retained_network.clear();
        self.unemitted_network.clear();
        self.retained_network_cursor = 0;
    }

    /// Yields the durable ledger from the uniquely owned engine exactly once.
    /// Called only after the durability fence passed (`DurablePending`); the
    /// coordinator's single `PublishDurable` effect consumes the result.
    pub fn durable_ledger(&mut self) -> Option<Arc<Ledger>> {
        self.engine
            .as_mut()
            .and_then(|engine| engine.durable_ledger())
    }

    /// Installs the seeded engine. Returns false when a plan already exists or
    /// the session is cancelled; a replacement engine never replaces a live
    /// traversal.
    pub fn install_engine(&mut self, engine: Box<dyn TreeEngine + Send + Sync>) -> bool {
        if self.cancelled || self.engine.is_some() {
            return false;
        }
        self.engine = Some(engine);
        true
    }

    /// Accepts a packet into the bounded mailbox. Returns false when the
    /// defensive budget is exhausted; the packet is dropped without mutation.
    pub fn push_packet(&mut self, packet: AdmittedLedgerPacket) -> bool {
        self.mailbox.push(packet)
    }

    /// Currently queued packet count.
    pub fn packet_count(&self) -> u64 {
        self.mailbox.packet_count()
    }

    /// Currently queued packet bytes.
    pub fn packet_bytes(&self) -> u64 {
        self.mailbox.packet_bytes()
    }

    /// The persistence state machine state.
    pub const fn persistence(&self) -> &SessionPersistence {
        &self.persistence
    }

    /// Deadline retries consumed so far.
    pub const fn timeouts(&self) -> u32 {
        self.timeouts
    }

    /// Bounded engine turns executed.
    pub const fn runs(&self) -> u64 {
        self.runs
    }

    /// Pending brokered NodeStore reads for this session.
    pub fn pending_read_count(&self) -> usize {
        self.pending_reads
            .len()
            .saturating_add(self.pending_recovery_reads.len())
    }

    /// Ordinary traversal reads participating in the current deferred-read
    /// barrier. Recovery reprobes are independent and do not hold this gate.
    pub fn pending_traversal_read_count(&self) -> usize {
        self.pending_reads.len()
    }

    /// Read needs waiting for bounded broker admission.
    pub fn read_backlog_count(&self) -> usize {
        self.read_backlog.len()
    }

    /// Pending network candidates requested from peers (observability).
    pub fn pending_network(&self) -> &BTreeSet<Uint256> {
        &self.pending_network
    }

    /// Exact current frontier retained for timeout recovery. These records are
    /// owned by this plan and never authorize work for another session.
    pub fn retained_network(&self) -> &[PlanNetworkNeed] {
        &self.retained_network
    }

    /// Removes the next normal outbound request batch from the exact retained
    /// frontier. The batch is FIFO and homogeneous by tree kind because one
    /// `TMGetLedger` request carries one node kind. A timeout never consumes
    /// this queue, so its existing rotating recovery selection remains eligible
    /// for every retained need. Passing zero preserves all queued work.
    pub fn take_next_normal_network_batch(&mut self, max_nodes: usize) -> Vec<PlanNetworkNeed> {
        if self.cancelled || max_nodes == 0 {
            return Vec::new();
        }
        let Some(first) = self.unemitted_network.pop_front() else {
            return Vec::new();
        };
        let kind = first.kind();
        let mut batch = vec![first];
        while batch.len() < max_nodes
            && self
                .unemitted_network
                .front()
                .is_some_and(|need| need.kind() == kind)
        {
            batch.push(
                self.unemitted_network
                    .pop_front()
                    .expect("checked FIFO frontier entry must remain present"),
            );
        }
        // rippled records only the truncated wire batch in recentNodes_, not
        // all candidates returned by getMissingNodes.
        self.recent_nodes
            .extend(batch.iter().map(|need| need.hash()));
        batch
    }

    /// Suspends only externally dispatched read identities while retaining the
    /// uniquely owned engine, mailbox, frontier, and backlog for a later exact
    /// session reactivation. Late read completions become stale; reactivation
    /// mints fresh operations before it resumes planning.
    pub fn suspend_for_dormancy(&mut self) {
        if let Some(engine) = self.engine.as_mut() {
            engine.rearm_pending_reads();
        }
        self.pending_reads.clear();
        self.pending_recovery_reads.clear();
    }

    /// True after cancellation cleared this plan.
    pub const fn is_cancelled(&self) -> bool {
        self.cancelled
    }

    /// Clears every queued and in-flight plan resource. After this, all `on_*`
    /// completions are stale and `run_turn` produces no work.
    pub fn cancel(&mut self) {
        self.cancelled = true;
        self.mailbox.clear();
        self.pending_reads.clear();
        self.pending_recovery_reads.clear();
        self.read_backlog.clear();
        self.network_backlog.clear();
        self.pending_network.clear();
        self.retained_network.clear();
        self.unemitted_network.clear();
        self.retained_network_cursor = 0;
        self.useful_peer_scores.clear();
        self.network_lanes.clear();
        self.recent_nodes.clear();
        self.engine = None;
        self.persistence = SessionPersistence::None;
    }

    /// Clear every external permit while preserving the engine's strong tree
    /// graph for rippled's one-minute terminal reuse window.
    pub fn terminalize_retaining_engine(&mut self) {
        self.cancelled = true;
        self.mailbox.clear();
        self.pending_reads.clear();
        self.pending_recovery_reads.clear();
        self.read_backlog.clear();
        self.network_backlog.clear();
        self.pending_network.clear();
        self.retained_network.clear();
        self.unemitted_network.clear();
        self.retained_network_cursor = 0;
        self.useful_peer_scores.clear();
        self.network_lanes.clear();
        self.recent_nodes.clear();
        self.persistence = SessionPersistence::None;
    }

    pub fn release_retained_engine(&mut self) {
        self.engine = None;
    }

    /// Records protocol progress for this plan. Progress suppresses recovery
    /// for the just-finished interval, but does not erase earlier no-progress
    /// timeouts. This matches rippled `InboundLedger::onTimer(wasProgress, ...)`.
    pub fn note_progress(&mut self) {
        self.progress_since_timeout = true;
    }

    /// Consumes the prior timeout interval's progress bit. A successful Base
    /// seed or useful node does not trigger rippled-style no-progress recovery
    /// at the immediately following timer; the next quiet interval does.
    pub fn take_no_progress_interval(&mut self) -> bool {
        !std::mem::replace(&mut self.progress_since_timeout, false)
    }

    /// Selects the next bounded retry batch from the exact current frontier.
    /// The cursor rotates before the following no-progress interval, so a
    /// frontier larger than `MAX_TIMEOUT_REPROBES` cannot be pinned behind its
    /// first request batch. Only retirement of an attached exact need or
    /// cancellation can change this retained frontier; incremental plan turns
    /// merge into it without resetting the cursor.
    pub fn next_timeout_recovery_batch(&mut self) -> Vec<PlanNetworkNeed> {
        let len = self.retained_network.len();
        if self.cancelled || len == 0 {
            return Vec::new();
        }
        self.retained_network_cursor %= len;
        let count = len.min(MAX_TIMEOUT_REPROBES);
        let start = self.retained_network_cursor;
        let batch = (0..count)
            .map(|offset| self.retained_network[(start + offset) % len])
            .collect();
        self.retained_network_cursor = (start + count) % len;
        batch
    }

    /// Submit brokered local re-probes for one exact timeout-recovery batch.
    /// The coordinator owns only logical tickets; NodeStore admission and
    /// physical I/O remain with the read port. Existing reads/backlog entries
    /// are never duplicated, and every retry gets a fresh exact operation
    /// identity. Callers reuse the same batch for peer resends.
    pub fn reprobe_network_batch(
        &mut self,
        retained: &[PlanNetworkNeed],
        ctx: &mut TurnContext,
    ) -> Vec<ReadRequest> {
        if self.cancelled || self.persistence != SessionPersistence::None {
            return Vec::new();
        }
        let Some(ledger_sequence) = self.ledger_sequence() else {
            return Vec::new();
        };
        let mut requests = Vec::new();
        for need in retained.iter().copied() {
            let hash = SHAMapHash::new(need.hash());
            if self
                .pending_recovery_reads
                .values()
                .any(|pending| *pending == need)
                || requests
                    .iter()
                    .any(|request: &ReadRequest| request.key() == hash)
                || self.pending_read_count().saturating_add(requests.len())
                    >= self.pending_reads_cap
            {
                continue;
            }
            let operation = OperationRef::new(
                ctx.session,
                OperationKind::RecoveryRead,
                ctx.ids.next_id(),
                ctx.ids.next_id(),
            );
            self.pending_recovery_reads.insert(operation, need);
            requests.push(ReadRequest::new(
                operation,
                hash,
                ledger_sequence,
                ctx.store_generation,
                ctx.priority,
            ));
        }
        requests
    }

    /// Runs one bounded work turn: drains the FIFO read-admission backlog,
    /// feeds a bounded batch of queued packets into the engine, then advances
    /// the engine up to `MAX_TURNS_PER_EVENT` times.
    pub fn run_turn(&mut self, ctx: &mut TurnContext) -> PlanTurn {
        if self.cancelled || self.persistence != SessionPersistence::None {
            return PlanTurn::Continue;
        }

        // Rippled processes one complete gmnProcessDeferredReads round before
        // activating parent resumes or discovering the next read/frontier
        // batch. Results may attach immediately, but no event may slide a
        // replacement read into this round while one ordinary operation is
        // still outstanding.
        if !self.pending_reads.is_empty() {
            return PlanTurn::Continue;
        }

        // Drain the FIFO admission backlog before further CPU work so history
        // over-admission cannot starve the bounded in-flight budget.
        if !self.read_backlog.is_empty() {
            let mut requests = Vec::new();
            while let Some(need) = self.read_backlog.pop_front() {
                if self.pending_reads.len() >= self.pending_reads_cap {
                    self.read_backlog.push_front(need);
                    break;
                }
                let operation = OperationRef::new(
                    ctx.session,
                    OperationKind::Read,
                    ctx.ids.next_id(),
                    ctx.ids.next_id(),
                );
                self.pending_reads.insert(need.hash, operation);
                requests.push(ReadRequest::new(
                    operation,
                    need.hash,
                    need.ledger_seq,
                    ctx.store_generation,
                    ctx.priority,
                ));
            }
            if requests.is_empty() {
                return PlanTurn::Continue;
            }
            return PlanTurn::Reads(requests);
        }

        if !self.network_backlog.is_empty() {
            let nodes = self.dispatch_network_backlog();
            if !nodes.is_empty() {
                return PlanTurn::Network(nodes);
            }
            // A full retained frontier must still admit queued peer packets:
            // an exact attachment can retire a slot and release preserved
            // backlog work. With no packet to apply, do not advance the tree
            // beyond undispatched output.
            if self.mailbox.is_empty() {
                return PlanTurn::Continue;
            }
        }

        let mut turns = 0u32;
        loop {
            turns += 1;
            if turns > MAX_TURNS_PER_EVENT {
                return PlanTurn::Continue;
            }
            let mut fed = PacketFeed::default();
            for _ in 0..MAX_PACKETS_FED_PER_TURN {
                let Some(engine) = self.engine.as_mut() else {
                    break;
                };
                let Some(packet) = self.mailbox.pop_front() else {
                    break;
                };
                fed.merge(Self::feed_packet(packet, &mut **engine));
            }
            for (peer, count) in &fed.useful_peer_counts {
                self.useful_peer_scores
                    .entry(*peer)
                    .and_modify(|current| *current = (*current).max(*count))
                    .or_insert(*count);
            }
            if self.mailbox.is_empty() && !self.useful_peer_scores.is_empty() {
                let scores = self
                    .useful_peer_scores
                    .iter()
                    .map(|(peer, count)| InboundLedgerPeerScore {
                        peer_id: peer.get(),
                        useful_count: *count,
                    })
                    .collect::<Vec<_>>();
                self.useful_peer_scores.clear();
                let was_empty = self.network_lanes.is_empty();
                for peer in select_inbound_ledger_reply_peers(&scores) {
                    let peer = PeerId::new(peer);
                    self.network_lanes.push_back(NetworkLane::Reply(peer));
                }
                if was_empty && !self.network_lanes.is_empty() && self.engine.is_some() {
                    self.reset_network_epoch();
                    self.engine
                        .as_mut()
                        .expect("engine presence checked before epoch reset")
                        .begin_reply_scan();
                }
            }
            // When a retained frontier is full, packet attachment is allowed
            // solely to retire exact needs and free one dispatch slot. Do not
            // advance the tree while older output is backlogged; that would
            // turn a bounded backlog into an unbounded hidden frontier.
            if !self.network_backlog.is_empty()
                && self.retained_network.len() >= MAX_RETAINED_NETWORK_FRONTIER
            {
                self.retire_network_resolutions(&fed.resolved_network);
                if fed.useful {
                    self.note_progress();
                }
                let nodes = self.dispatch_network_backlog();
                if !nodes.is_empty() {
                    return PlanTurn::Network(nodes);
                }
                return PlanTurn::Continue;
            }
            let (outcome, useful_peer_data, ready_continues, pending_writes, ledger_sequence) = {
                let Some(engine) = self.engine.as_mut() else {
                    // No rooted plan yet; queued packets wait in the mailbox.
                    return PlanTurn::Continue;
                };
                let before = engine.branch_steps();
                let useful_peer_data = fed.useful;
                let outcome = engine.advance(MAX_NEW_READS_PER_PASS);
                let ready_continues = fed.attached
                    || (engine.has_runnable_frontier() && engine.branch_steps() > before);
                let pending_writes = if matches!(outcome, PlanStepOutcome::Complete) {
                    Vec::new()
                } else {
                    engine.take_persistable_nodes()
                };
                (
                    outcome,
                    useful_peer_data,
                    ready_continues,
                    pending_writes,
                    engine.ledger_sequence(),
                )
            };
            self.runs += 1;
            self.retire_network_resolutions(&fed.resolved_network);
            if fed.nodes_seen != 0 {
                tracing::trace!(
                    target: "acquisition_trace",
                    event = "packet_batch_applied",
                    run_epoch = ctx.session.run_epoch().get(),
                    session_id = ctx.session.session_id().get(),
                    target_hash = %ctx.session.target_hash(),
                    plan_epoch = ctx.session.plan_epoch().get(),
                    store_generation = ctx.session.store_generation().get(),
                    plan_run = self.runs,
                    nodes_seen = fed.nodes_seen,
                    malformed_nodes = fed.malformed_nodes,
                    attached = fed.attached,
                    useful = fed.useful,
                    mailbox_packets = self.mailbox.packet_count(),
                    mailbox_bytes = self.mailbox.packet_bytes(),
                    pending_network = self.pending_network.len(),
                    "acquisition trace: bounded peer-node batch applied to SHAMap plan"
                );
            }
            // Matches rippled `InboundLedger::processData`: only useful peer
            // data resets the no-progress timeout. A duplicate, stale, or
            // unattached but decodable packet may wake the frontier but cannot
            // conceal an acquisition stall.
            if useful_peer_data {
                self.note_progress();
            }
            if !pending_writes.is_empty() {
                // `TreePlan::advance` transfers newly discovered missing hashes
                // into its returned effect. Incremental persistence must not
                // discard that effect: retain it until this write settles, then
                // drain it before another CPU turn. This preserves the async
                // NodeStore boundary and rippled's `InboundLedger::trigger`
                // guarantee (src/xrpld/app/ledger/detail/InboundLedger.cpp)
                // that a scan's missing-node work remains live after storing
                // accepted data.
                let deferred_reads = match &outcome {
                    PlanStepOutcome::NeedsReads(needs) => {
                        self.defer_reads_after_incremental_write(needs.iter().cloned())
                    }
                    _ => 0,
                };
                let deferred_network = match &outcome {
                    PlanStepOutcome::NeedsNetwork(nodes) => {
                        self.defer_network_after_incremental_write(nodes.iter().copied())
                    }
                    _ => 0,
                };
                if deferred_reads != 0 || deferred_network != 0 {
                    tracing::trace!(
                        target: "acquisition_trace",
                        event = "effects_deferred_for_incremental_write",
                        run_epoch = ctx.session.run_epoch().get(),
                        session_id = ctx.session.session_id().get(),
                        target_hash = %ctx.session.target_hash(),
                        plan_epoch = ctx.session.plan_epoch().get(),
                        store_generation = ctx.session.store_generation().get(),
                        deferred_reads,
                        deferred_network,
                        read_backlog = self.read_backlog.len(),
                        network_backlog = self.network_backlog.len(),
                        "acquisition trace: retained traversal effects until incremental NodeStore write completes"
                    );
                }
                let Some(ledger_sequence) = ledger_sequence.filter(|sequence| *sequence != 0)
                else {
                    return PlanTurn::Invalid;
                };
                let operation = OperationRef::new(
                    ctx.session,
                    OperationKind::Write,
                    ctx.ids.next_id(),
                    ctx.ids.next_id(),
                );
                self.persistence = SessionPersistence::IncrementalWritePending { operation };
                return PlanTurn::Persist(WriteBatch::incremental(
                    operation,
                    ctx.store_generation,
                    ledger_sequence,
                    pending_writes,
                ));
            }
            match outcome {
                PlanStepOutcome::Ready => {
                    if ready_continues {
                        continue;
                    }
                    return PlanTurn::Continue;
                }
                PlanStepOutcome::NeedsReads(needs) => {
                    let requests = self.admit_reads(needs, ctx);
                    if requests.is_empty() {
                        return PlanTurn::Continue;
                    }
                    return PlanTurn::Reads(requests);
                }
                PlanStepOutcome::NeedsNetwork(nodes) => {
                    self.enqueue_network_frontier(nodes);
                    let nodes = self.dispatch_network_backlog();
                    if nodes.is_empty() {
                        return PlanTurn::Continue;
                    }
                    return PlanTurn::Network(nodes);
                }
                PlanStepOutcome::Complete => return self.on_complete(ctx),
                PlanStepOutcome::Invalid => return PlanTurn::Invalid,
            }
        }
    }

    /// Applies one normal traversal read or exact timeout recovery-read
    /// completion. A recovery completion is accepted only for its matching
    /// operation and retained `(node id, hash, kind)` need; ordinary reads
    /// never forge that association.
    pub fn on_read(&mut self, completion: &ReadCompletion) -> PlanReadOutcome {
        let operation = completion.operation();
        if self.engine.is_none() {
            return PlanReadOutcome::Stale;
        }
        match operation.kind() {
            OperationKind::Read => {
                let Some((&hash, _)) = self
                    .pending_reads
                    .iter()
                    .find(|(_, expected)| expected.is_expected_for(&operation))
                else {
                    return PlanReadOutcome::Stale;
                };
                self.pending_reads.remove(&hash);
                let applied = self
                    .engine
                    .as_mut()
                    .expect("checked rooted engine")
                    .apply_read(hash, completion.outcome());
                // In rippled all 512-read rounds execute synchronously inside
                // one getMissingNodes trigger, so the acquisition cannot time
                // out between successful local attachments. Quaxar externalizes
                // those rounds; count a verified attachment as interval progress
                // or a large local reconstruction is repeatedly cancelled while
                // its private root graph is actively growing.
                if matches!(
                    applied,
                    PlanReadApply::Applied {
                        attached_edges: 1..,
                        ..
                    }
                ) {
                    self.note_progress();
                }
                // An ordinary read is keyed only by hash and may cover several
                // retained locations. It must not retire a frontier entry
                // without the exact `PlanNetworkNeed` verification provided by
                // a recovery read or an attached peer node.
                PlanReadOutcome::Applied
            }
            OperationKind::RecoveryRead => {
                let Some(need) = self.pending_recovery_reads.remove(&operation) else {
                    return PlanReadOutcome::Stale;
                };
                let applied = self
                    .engine
                    .as_mut()
                    .expect("checked rooted engine")
                    .apply_recovery_read(need, completion.outcome());
                if matches!(applied, PlanReadApply::Applied { .. }) {
                    self.retire_network_need(need);
                }
                if matches!(
                    applied,
                    PlanReadApply::Applied {
                        attached_edges: 1..,
                        ..
                    }
                ) {
                    self.note_progress();
                }
                PlanReadOutcome::Applied
            }
            _ => PlanReadOutcome::Stale,
        }
    }

    /// Applies one write completion. An incremental accepted-node write
    /// returns the plan to active work; only a final write advances to its
    /// durability fence. Shared engine completion metadata is released only
    /// after the exact write acceptance.
    pub fn on_write(&mut self, operation: OperationRef, outcome: WriteOutcome) -> PlanWriteOutcome {
        if operation.kind() != OperationKind::Write {
            return PlanWriteOutcome::Stale;
        }
        match &self.persistence {
            SessionPersistence::IncrementalWritePending {
                operation: expected,
            } if expected.is_expected_for(&operation) => match outcome {
                WriteOutcome::Accepted => {
                    self.persistence = SessionPersistence::None;
                    if let Some(engine) = self.engine.as_mut() {
                        engine.on_persistence_accepted();
                    }
                    PlanWriteOutcome::IncrementalAccepted
                }
                WriteOutcome::Failed => {
                    self.persistence = SessionPersistence::Failed {
                        reason: FailureReason::WriteFailure,
                    };
                    PlanWriteOutcome::Failed(FailureReason::WriteFailure)
                }
                WriteOutcome::Cancelled => {
                    self.persistence = SessionPersistence::None;
                    PlanWriteOutcome::Cancelled(CancelReason::StoreRotated)
                }
                WriteOutcome::Stale => PlanWriteOutcome::Stale,
            },
            SessionPersistence::FinalWritePending {
                operation: expected,
                fence,
            } if expected.is_expected_for(&operation) => match outcome {
                WriteOutcome::Accepted => {
                    let fence = *fence;
                    self.persistence = SessionPersistence::FencePending { operation: fence };
                    if let Some(engine) = self.engine.as_mut() {
                        engine.on_persistence_accepted();
                    }
                    PlanWriteOutcome::FinalAccepted
                }
                WriteOutcome::Failed => {
                    self.persistence = SessionPersistence::Failed {
                        reason: FailureReason::WriteFailure,
                    };
                    PlanWriteOutcome::Failed(FailureReason::WriteFailure)
                }
                WriteOutcome::Cancelled => {
                    self.persistence = SessionPersistence::None;
                    PlanWriteOutcome::Cancelled(CancelReason::StoreRotated)
                }
                WriteOutcome::Stale => PlanWriteOutcome::Stale,
            },
            _ => PlanWriteOutcome::Stale,
        }
    }

    /// Applies one ordered NodeStore-acceptance completion. `FencePending`
    /// moves to `Durable` only after the final batch was accepted; a failure
    /// terminalizes intent. Physical sync remains backend lifecycle policy.
    pub fn on_durability(
        &mut self,
        operation: OperationRef,
        outcome: DurabilityOutcome,
    ) -> PlanDurabilityOutcome {
        if operation.kind() != OperationKind::DurabilityFence {
            return PlanDurabilityOutcome::Stale;
        }
        match &self.persistence {
            SessionPersistence::FencePending {
                operation: expected,
            } if expected.is_expected_for(&operation) => match outcome {
                DurabilityOutcome::Passed => {
                    self.persistence = SessionPersistence::Durable;
                    PlanDurabilityOutcome::Durable
                }
                DurabilityOutcome::Failed => {
                    self.persistence = SessionPersistence::Failed {
                        reason: FailureReason::DurabilityFenceFailed,
                    };
                    PlanDurabilityOutcome::Failed(FailureReason::DurabilityFenceFailed)
                }
                DurabilityOutcome::Stale => PlanDurabilityOutcome::Stale,
            },
            _ => PlanDurabilityOutcome::Stale,
        }
    }

    /// Applies one deadline interval. Only a no-progress interval consumes
    /// timeout budget. rippled permits six no-progress recovery intervals and
    /// fails on the seventh (`InboundLedger::onTimer` plus TimeoutCounter), so
    /// the counter is not reset by progress and fails only after exceeding the
    /// configured recovery budget. A cancelled plan stays terminal.
    pub fn on_timeout(&mut self, no_progress: bool) -> PlanTimeout {
        if self.cancelled {
            return PlanTimeout::Fail;
        }
        if !no_progress {
            return PlanTimeout::Continue;
        }
        self.timeouts = self.timeouts.saturating_add(1);
        if self.timeouts > self.max_timeouts {
            self.cancelled = true;
            PlanTimeout::Fail
        } else {
            PlanTimeout::Continue
        }
    }

    /// Deserializes and routes one packet through the ledger map and retained
    /// frontier. Useful-data credit is separate from attachment so only the
    /// former resets the inbound timeout, matching rippled.
    fn feed_packet(mut packet: AdmittedLedgerPacket, engine: &mut dyn TreeEngine) -> PacketFeed {
        let peer = packet.peer_id();
        let kind = match packet.packet().packet_type {
            InboundLedgerDataType::StateNode => TreeKind::State,
            InboundLedgerDataType::TransactionNode => TreeKind::Transaction,
            InboundLedgerDataType::Base => {
                // The header packet seeded the engine; it is not a tree node.
                let _ = packet.settle();
                return PacketFeed::default();
            }
        };
        let mut fed = PacketFeed::default();
        for node in &packet.packet().nodes {
            fed.nodes_seen = fed.nodes_seen.saturating_add(1);
            let decoded = match SHAMapTreeNode::make_from_wire(&node.node_data) {
                Ok(Some(decoded)) => decoded,
                Ok(None) | Err(_) => {
                    fed.malformed_nodes = fed.malformed_nodes.saturating_add(1);
                    tracing::warn!(
                        target: "acquisition",
                        packet_type = ?packet.packet().packet_type,
                        wire_bytes = node.node_data.len(),
                        wire_type = node.node_data.last().copied(),
                        "Rejected malformed ledger tree-node payload"
                    );
                    break;
                }
            };
            if decoded.get_hash().is_zero() {
                fed.malformed_nodes = fed.malformed_nodes.saturating_add(1);
                break;
            }
            let applied = engine.apply_network_node(kind, node);
            if applied.is_invalid() {
                fed.malformed_nodes = fed.malformed_nodes.saturating_add(1);
                break;
            }
            if applied.attached()
                && let Some(node_id) = node.node_id.as_deref().and_then(deserialize_shamap_node_id)
            {
                fed.resolved_network.push(PlanNetworkNeed::new(
                    node_id,
                    *decoded.get_hash().as_uint256(),
                    kind,
                ));
            }
            fed.attached |= applied.attached();
            fed.useful |= applied.is_useful();
            if applied.is_useful() {
                fed.useful_peer_counts
                    .entry(peer)
                    .and_modify(|count| *count = count.saturating_add(1))
                    .or_insert(1);
            }
        }
        let _ = packet.settle();
        fed
    }

    /// Retains a read effect while the incremental write from the same plan
    /// turn settles. The traversal already transferred these needs out of its
    /// unannounced set, so losing them would permanently strand its pending
    /// edges.
    fn defer_reads_after_incremental_write(
        &mut self,
        needs: impl IntoIterator<Item = PlanReadNeed>,
    ) -> usize {
        let mut deferred = 0;
        for need in needs {
            if self.pending_reads.contains_key(&need.hash)
                || self
                    .read_backlog
                    .iter()
                    .any(|queued| queued.hash == need.hash)
            {
                continue;
            }
            self.read_backlog.push_back(need);
            deferred += 1;
        }
        deferred
    }

    /// Retains a peer effect while the incremental write from the same plan
    /// turn settles. `TreePlan` emits these candidates once, so queueing them
    /// preserves the retained traversal frontier across the write boundary.
    fn defer_network_after_incremental_write(
        &mut self,
        nodes: impl IntoIterator<Item = PlanNetworkNeed>,
    ) -> usize {
        let mut deferred = 0;
        for node in nodes {
            if self.recent_nodes.contains(&node.hash()) {
                continue;
            }
            if self.retained_network.contains(&node)
                || self.network_backlog.iter().any(|queued| *queued == node)
            {
                continue;
            }
            self.network_backlog.push_back(node);
            deferred += 1;
        }
        self.refresh_pending_network();
        deferred
    }

    /// Queues exact current frontier work without discarding a later batch
    /// when the retained dispatch window is full. Identity is the complete
    /// `(node id, hash, kind)`; duplicate announcements are ignored.
    fn enqueue_network_frontier(&mut self, nodes: impl IntoIterator<Item = PlanNetworkNeed>) {
        for node in nodes {
            if self.recent_nodes.contains(&node.hash()) {
                continue;
            }
            if self.retained_network.contains(&node)
                || self.network_backlog.iter().any(|queued| *queued == node)
            {
                continue;
            }
            self.network_backlog.push_back(node);
        }
        self.refresh_pending_network();
    }

    /// Moves only the capacity that is currently available into the exact
    /// retained frontier. The remaining backlog stays intact until an exact
    /// attachment retires a slot; `run_turn` will not advance the engine while
    /// it remains, which bounds it to one TreePlan-emitted batch.
    fn dispatch_network_backlog(&mut self) -> Vec<PlanNetworkNeed> {
        let capacity = MAX_RETAINED_NETWORK_FRONTIER.saturating_sub(self.retained_network.len());
        let mut dispatched = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            let Some(node) = self.network_backlog.pop_front() else {
                break;
            };
            self.retained_network.push(node);
            self.unemitted_network.push_back(node);
            dispatched.push(node);
        }
        self.normalize_retained_network_cursor();
        self.refresh_pending_network();
        dispatched
    }

    /// Retires only exact retained/backlogged needs whose peer packet both
    /// attached and carried the matching node id, hash, and tree kind. A hash
    /// match by itself must not erase another still-blocked tree location.
    fn retire_network_resolutions(&mut self, resolutions: &[PlanNetworkNeed]) {
        self.retained_network
            .retain(|need| !resolutions.contains(need));
        self.unemitted_network
            .retain(|need| !resolutions.contains(need));
        self.network_backlog
            .retain(|need| !resolutions.contains(need));
        self.normalize_retained_network_cursor();
        self.refresh_pending_network();
    }

    /// Retires only the exact retained/backlogged need whose recovery read
    /// attached. Equal hashes at different node ids or in different trees
    /// remain eligible until independently verified.
    fn retire_network_need(&mut self, resolved: PlanNetworkNeed) {
        self.retained_network.retain(|need| *need != resolved);
        self.unemitted_network.retain(|need| *need != resolved);
        self.network_backlog.retain(|need| *need != resolved);
        self.normalize_retained_network_cursor();
        self.refresh_pending_network();
    }

    fn refresh_pending_network(&mut self) {
        self.pending_network.clear();
        self.pending_network
            .extend(self.retained_network.iter().map(|need| need.hash()));
        self.pending_network
            .extend(self.network_backlog.iter().map(|need| need.hash()));
    }

    fn normalize_retained_network_cursor(&mut self) {
        if self.retained_network.is_empty() {
            self.retained_network_cursor = 0;
        } else {
            self.retained_network_cursor %= self.retained_network.len();
        }
    }

    /// Admits newly announced reads up to the pending cap. Hashes already in
    /// flight are skipped; overflow goes to the FIFO backlog for a later turn.
    fn admit_reads(&mut self, needs: Vec<PlanReadNeed>, ctx: &mut TurnContext) -> Vec<ReadRequest> {
        let mut requests = Vec::new();
        for need in needs {
            if self.pending_reads.contains_key(&need.hash) {
                continue;
            }
            if self.pending_reads.len() >= self.pending_reads_cap {
                self.read_backlog.push_back(need);
                continue;
            }
            let operation = OperationRef::new(
                ctx.session,
                OperationKind::Read,
                ctx.ids.next_id(),
                ctx.ids.next_id(),
            );
            self.pending_reads.insert(need.hash, operation);
            requests.push(ReadRequest::new(
                operation,
                need.hash,
                need.ledger_seq,
                ctx.store_generation,
                ctx.priority,
            ));
        }
        requests
    }

    /// Transitions to final persistence once the tree is complete. Earlier
    /// accepted writes were already submitted incrementally; this final batch
    /// drains the remainder and is the only one carrying a durability fence.
    fn on_complete(&mut self, ctx: &mut TurnContext) -> PlanTurn {
        let Some(ledger_sequence) = self
            .engine
            .as_ref()
            .and_then(|engine| engine.persistence_sequence())
            .filter(|sequence| *sequence != 0)
        else {
            return PlanTurn::Invalid;
        };
        let nodes = self
            .engine
            .as_mut()
            .map(|engine| engine.take_persistable_nodes())
            .unwrap_or_default();
        let write_op = OperationRef::new(
            ctx.session,
            OperationKind::Write,
            ctx.ids.next_id(),
            ctx.ids.next_id(),
        );
        let fence_op = OperationRef::new(
            ctx.session,
            OperationKind::DurabilityFence,
            ctx.ids.next_id(),
            ctx.ids.next_id(),
        );
        self.persistence = SessionPersistence::FinalWritePending {
            operation: write_op,
            fence: fence_op,
        };
        PlanTurn::Persist(WriteBatch::new(
            write_op,
            fence_op,
            ctx.store_generation,
            ledger_sequence,
            nodes,
        ))
    }
}

/// A deterministic scripted [`TreeEngine`] for tests. Each `advance` consumes
/// one scripted step; read/network applications mark the frontier runnable so
/// the next step is consumed on the next turn (mirroring real continuation
/// behavior).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScriptedStep {
    /// Announce these reads on the next advance.
    NeedsReads(Vec<PlanReadNeed>),
    /// Announce legacy network candidates as State nodes on the next advance.
    /// Existing tuple scripts retain their previous State behavior; tests that
    /// need transaction preservation use [`Self::NeedsNetworkWithKind`].
    NeedsNetwork(Vec<(SHAMapNodeId, Uint256)>),
    /// Announce explicitly kind-qualified network candidates on the next
    /// advance.
    NeedsNetworkWithKind(Vec<PlanNetworkNeed>),
    /// Complete the tree on the next advance.
    Complete,
    /// Produce an invalid plan on the next advance.
    Invalid,
}

/// A deterministic [`TreeEngine`] fake driven by a script.
#[derive(Debug)]
pub struct ScriptedEngine {
    plan_id: TreePlanId,
    steps: VecDeque<ScriptedStep>,
    runnable_frontier: bool,
    branch_steps: u64,
    applied_reads: u64,
    applied_nodes: u64,
    persistable: Vec<PersistNode>,
    persistence_acceptance_counter: Option<Arc<std::sync::atomic::AtomicUsize>>,
    durable_ledger: Option<Arc<Ledger>>,
    persistence_sequence: Option<u32>,
}

impl ScriptedEngine {
    /// Builds a scripted engine.
    pub fn new(
        plan_id: TreePlanId,
        steps: impl IntoIterator<Item = ScriptedStep>,
        persistable: Vec<PersistNode>,
    ) -> Self {
        let steps: VecDeque<_> = steps.into_iter().collect();
        let runnable_frontier = !steps.is_empty();
        Self {
            plan_id,
            steps,
            runnable_frontier,
            branch_steps: 0,
            applied_reads: 0,
            applied_nodes: 0,
            persistable,
            persistence_acceptance_counter: None,
            durable_ledger: None,
            persistence_sequence: None,
        }
    }

    /// Sets the verified header sequence used if this scripted engine reaches
    /// persistence. Tests must opt in rather than silently using a placeholder.
    pub fn with_persistence_sequence(mut self, sequence: u32) -> Self {
        self.persistence_sequence = (sequence != 0).then_some(sequence);
        self
    }

    /// Records accepted write acknowledgements for deterministic persistence
    /// ordering tests.
    pub fn with_persistence_acceptance_counter(
        mut self,
        counter: Arc<std::sync::atomic::AtomicUsize>,
    ) -> Self {
        self.persistence_acceptance_counter = Some(counter);
        self
    }

    /// Attaches a durable ledger the engine yields exactly once at the M5
    /// durable handoff.
    pub fn with_durable_ledger(mut self, ledger: Arc<Ledger>) -> Self {
        self.durable_ledger = Some(ledger);
        self
    }

    /// Reads applied to this engine.
    pub const fn applied_reads(&self) -> u64 {
        self.applied_reads
    }

    /// Network nodes applied to this engine.
    pub const fn applied_nodes(&self) -> u64 {
        self.applied_nodes
    }
}

impl TreeEngine for ScriptedEngine {
    fn plan_id(&self) -> TreePlanId {
        self.plan_id
    }

    fn advance(&mut self, _max_new_reads: usize) -> PlanStepOutcome {
        self.runnable_frontier = false;
        match self.steps.pop_front() {
            Some(ScriptedStep::NeedsReads(needs)) => PlanStepOutcome::NeedsReads(needs),
            Some(ScriptedStep::NeedsNetwork(nodes)) => PlanStepOutcome::NeedsNetwork(
                nodes
                    .into_iter()
                    .map(|(node_id, hash)| PlanNetworkNeed::new(node_id, hash, TreeKind::State))
                    .collect(),
            ),
            Some(ScriptedStep::NeedsNetworkWithKind(nodes)) => PlanStepOutcome::NeedsNetwork(nodes),
            Some(ScriptedStep::Complete) => PlanStepOutcome::Complete,
            Some(ScriptedStep::Invalid) => PlanStepOutcome::Invalid,
            None => PlanStepOutcome::Ready,
        }
    }

    fn apply_read(&mut self, _hash: SHAMapHash, _outcome: &ReadOutcome) -> PlanReadApply {
        self.applied_reads += 1;
        self.branch_steps += 1;
        self.runnable_frontier = !self.steps.is_empty();
        PlanReadApply::Applied {
            attached_edges: 1,
            missing_edges: 0,
        }
    }

    fn apply_recovery_read(
        &mut self,
        _need: PlanNetworkNeed,
        outcome: &ReadOutcome,
    ) -> PlanReadApply {
        match outcome {
            ReadOutcome::Settled { node: Some(_) } => {
                self.applied_reads += 1;
                self.branch_steps += 1;
                self.runnable_frontier = !self.steps.is_empty();
                PlanReadApply::Applied {
                    attached_edges: 1,
                    missing_edges: 0,
                }
            }
            ReadOutcome::Settled { node: None } => PlanReadApply::UnknownRead,
            ReadOutcome::Stale | ReadOutcome::Cancelled => PlanReadApply::Cancelled,
        }
    }

    fn apply_network_node(
        &mut self,
        _kind: TreeKind,
        _node: &InboundLedgerNodeData,
    ) -> PlanNetworkApply {
        self.applied_nodes += 1;
        self.branch_steps += 1;
        self.runnable_frontier = !self.steps.is_empty();
        PlanNetworkApply::new(
            PlanReadApply::Applied {
                attached_edges: 1,
                missing_edges: 0,
            },
            true,
        )
    }

    fn has_runnable_frontier(&self) -> bool {
        self.runnable_frontier
    }

    fn branch_steps(&self) -> u64 {
        self.branch_steps
    }

    fn ledger_sequence(&self) -> Option<u32> {
        self.persistence_sequence
    }

    fn take_persistable_nodes(&mut self) -> Vec<PersistNode> {
        std::mem::take(&mut self.persistable)
    }

    fn on_persistence_accepted(&mut self) {
        if let Some(counter) = &self.persistence_acceptance_counter {
            counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }

    fn persistence_sequence(&self) -> Option<u32> {
        self.persistence_sequence
    }

    fn durable_ledger(&mut self) -> Option<Arc<Ledger>> {
        self.durable_ledger.take()
    }
}

/// A real [`TreeEngine`] over the ledger `TreePlan` traversal. M4.1 uses it in
/// deterministic fixtures (rooted tree + [`NullResident`]); the app adapter
/// supplies persistable nodes with the M4.2 wiring.
#[derive(Debug)]
pub struct LedgerTreePlanEngine {
    plan: TreePlan,
    persistable: Vec<PersistNode>,
}

impl LedgerTreePlanEngine {
    /// Wraps a ledger `TreePlan`.
    pub fn new(plan: TreePlan) -> Self {
        Self {
            plan,
            persistable: Vec::new(),
        }
    }

    /// The wrapped traversal plan.
    pub const fn plan(&self) -> &TreePlan {
        &self.plan
    }
}

impl TreeEngine for LedgerTreePlanEngine {
    fn plan_id(&self) -> TreePlanId {
        self.plan.id()
    }

    fn advance(&mut self, max_new_reads: usize) -> PlanStepOutcome {
        let mut first_child = || rand_int_to(255u8);
        let mut yield_now = || false;
        match self.plan.advance_with_yield(
            max_new_reads,
            &mut NullResident,
            &mut first_child,
            &mut yield_now,
        ) {
            TreeAdvance::Ready => PlanStepOutcome::Ready,
            TreeAdvance::NeedsReads(reads) => PlanStepOutcome::NeedsReads(
                reads
                    .into_iter()
                    .map(|need| {
                        PlanReadNeed::new(
                            need.hash(),
                            need.ledger_seq(),
                            need.node_id(),
                            need.branch(),
                        )
                    })
                    .collect(),
            ),
            TreeAdvance::NeedsNetwork(nodes) => PlanStepOutcome::NeedsNetwork(
                nodes
                    .into_iter()
                    .map(|(node_id, hash)| PlanNetworkNeed::new(node_id, hash, self.plan.kind()))
                    .collect(),
            ),
            TreeAdvance::Complete => PlanStepOutcome::Complete,
            TreeAdvance::Invalid => PlanStepOutcome::Invalid,
        }
    }

    fn apply_read(&mut self, hash: SHAMapHash, outcome: &ReadOutcome) -> PlanReadApply {
        let missing = match outcome {
            ReadOutcome::Settled { node: Some(bytes) } => {
                match SHAMapTreeNode::make_from_wire(bytes) {
                    Ok(Some(node)) => MissingNodeReadOutcome::Found(node),
                    Ok(None) => MissingNodeReadOutcome::Miss,
                    Err(_) => return PlanReadApply::UnknownRead,
                }
            }
            ReadOutcome::Settled { node: None } => MissingNodeReadOutcome::Miss,
            ReadOutcome::Stale | ReadOutcome::Cancelled => MissingNodeReadOutcome::Cancelled,
        };
        Self::map_apply(self.plan.apply_read_result(self.plan.id(), hash, missing))
    }

    fn apply_recovery_read(
        &mut self,
        need: PlanNetworkNeed,
        outcome: &ReadOutcome,
    ) -> PlanReadApply {
        if self.plan.kind() != need.kind() {
            return PlanReadApply::StalePlan;
        }
        let node = match outcome {
            ReadOutcome::Settled { node: Some(bytes) } => {
                match SHAMapTreeNode::make_from_prefix(bytes, SHAMapHash::new(need.hash())) {
                    Ok(node) if *node.get_hash().as_uint256() == need.hash() => node,
                    _ => return PlanReadApply::HashMismatch,
                }
            }
            ReadOutcome::Settled { node: None } => return PlanReadApply::UnknownRead,
            ReadOutcome::Stale | ReadOutcome::Cancelled => return PlanReadApply::Cancelled,
        };
        Self::map_apply(self.plan.apply_network_node(
            self.plan.id(),
            SHAMapHash::new(need.hash()),
            node,
        ))
    }

    fn apply_network_node(
        &mut self,
        kind: TreeKind,
        node: &InboundLedgerNodeData,
    ) -> PlanNetworkApply {
        if self.plan.kind() != kind {
            return PlanNetworkApply::new(PlanReadApply::StalePlan, false);
        }
        let Ok(Some(decoded)) = SHAMapTreeNode::make_from_wire(&node.node_data) else {
            return PlanNetworkApply::new(PlanReadApply::UnknownRead, false);
        };
        let Some(node_id) = node.node_id.as_deref().and_then(deserialize_shamap_node_id) else {
            return PlanNetworkApply::invalid(PlanReadApply::UnknownRead, false);
        };
        let hash = decoded.get_hash();
        let attachment = Self::map_apply(self.plan.apply_known_network_node(
            self.plan.id(),
            node_id,
            hash,
            decoded,
        ));
        let useful = matches!(attachment, PlanReadApply::Applied { .. });
        if matches!(attachment, PlanReadApply::HashMismatch) {
            PlanNetworkApply::invalid(attachment, useful)
        } else {
            PlanNetworkApply::new(attachment, useful)
        }
    }

    fn begin_reply_scan(&mut self) {
        self.plan.begin_reply_scan();
    }

    fn retain_network_needs(&mut self, needs: &[PlanNetworkNeed]) {
        self.plan
            .retain_network_hashes(needs.iter().map(|need| SHAMapHash::new(need.hash())));
    }

    fn rearm_pending_reads(&mut self) {
        self.plan.rearm_pending_reads();
    }

    fn has_runnable_frontier(&self) -> bool {
        self.plan.has_runnable_frontier()
    }

    fn branch_steps(&self) -> u64 {
        self.plan.branch_steps()
    }

    fn take_persistable_nodes(&mut self) -> Vec<PersistNode> {
        std::mem::take(&mut self.persistable)
    }

    fn persistence_sequence(&self) -> Option<u32> {
        None
    }

    fn durable_ledger(&mut self) -> Option<Arc<Ledger>> {
        None
    }
}

impl LedgerTreePlanEngine {
    fn map_apply(apply: MissingNodeReadApply) -> PlanReadApply {
        match apply {
            MissingNodeReadApply::Applied {
                attached_edges,
                missing_edges,
            } => PlanReadApply::Applied {
                attached_edges,
                missing_edges,
            },
            MissingNodeReadApply::Requeued => PlanReadApply::Requeued,
            MissingNodeReadApply::Cancelled => PlanReadApply::Cancelled,
            MissingNodeReadApply::StalePlan => PlanReadApply::StalePlan,
            MissingNodeReadApply::HashMismatch => PlanReadApply::HashMismatch,
            MissingNodeReadApply::UnknownRead => PlanReadApply::UnknownRead,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{
        IdCounter, OperationGeneration, OperationId, PeerId, PlanEpoch, RunEpoch, SessionId,
    };
    use crate::ingress::{AdmissionGate, BackpressureOutcome};
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::make_shared_intrusive;
    use bytes::Bytes;
    use ledger::{InboundLedgerNodeData, TreeKind};
    use shamap::nodes::item::SHAMapItem;
    use shamap::sync::{SyncState, SyncTree};
    use shamap::tree_node::SHAMapTreeNode;

    fn session() -> SessionRef {
        SessionRef::new(
            RunEpoch::new(1),
            SessionId::new(1),
            Uint256::from(1),
            PlanEpoch::new(1),
            StoreGeneration::new(1),
        )
    }

    fn budget() -> AdmissionBudget {
        AdmissionBudget::new(128, 4 * 1024 * 1024)
    }

    fn ctx<'a>(session: SessionRef, ids: &'a mut IdCounter) -> TurnContext<'a> {
        TurnContext {
            session,
            store_generation: StoreGeneration::new(1),
            priority: ReadPriority::Consensus,
            ids,
        }
    }

    fn need(hash: u64) -> PlanReadNeed {
        PlanReadNeed::new(
            SHAMapHash::new(Uint256::from(hash)),
            1,
            SHAMapNodeId::default(),
            0,
        )
    }

    fn packet(session: SessionRef, budget: AdmissionBudget, bytes: u64) -> AdmittedLedgerPacket {
        let gate = Arc::new(AdmissionGate::new(budget, session));
        let lease = match gate.try_reserve(1, bytes) {
            BackpressureOutcome::Admitted(lease) => lease,
            other => panic!("expected admission, got {other:?}"),
        };
        AdmittedLedgerPacket::new(
            lease,
            session,
            PeerId::new(1),
            ledger::InboundLedgerPacket::new(
                ledger::InboundLedgerDataType::StateNode,
                vec![InboundLedgerNodeData::new(None, vec![0; bytes as usize])],
            ),
        )
        .expect("matching lease must admit")
    }

    fn scripted(plan_id: u64, steps: Vec<ScriptedStep>) -> SessionPlan {
        let mut plan = SessionPlan::new(budget());
        assert!(
            plan.install_engine(Box::new(
                ScriptedEngine::new(TreePlanId::new(plan_id), steps, Vec::new(),)
                    .with_persistence_sequence(1)
            ))
        );
        plan
    }

    fn persistence_probe(counter: Arc<std::sync::atomic::AtomicUsize>) -> SessionPlan {
        let mut plan = SessionPlan::new(budget());
        assert!(
            plan.install_engine(Box::new(
                ScriptedEngine::new(
                    TreePlanId::new(1),
                    Vec::new(),
                    vec![PersistNode::new(
                        SHAMapHash::new(Uint256::from(99)),
                        Bytes::from_static(b"accepted-node"),
                        crate::io::StoredObjectKind::AccountNode,
                    )],
                )
                .with_persistence_sequence(1)
                .with_persistence_acceptance_counter(counter),
            ))
        );
        plan
    }

    #[test]
    fn write_acceptance_hook_ignores_nonaccepted_outcomes() {
        let mut ids = IdCounter::new();
        let s = session();
        let accepted_writes = Arc::new(std::sync::atomic::AtomicUsize::new(0));

        let mut failed = persistence_probe(Arc::clone(&accepted_writes));
        let PlanTurn::Persist(write) = failed.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected incremental persist");
        };
        assert_eq!(
            failed.on_write(write.operation(), WriteOutcome::Failed),
            PlanWriteOutcome::Failed(FailureReason::WriteFailure)
        );

        let mut stale = persistence_probe(Arc::clone(&accepted_writes));
        let PlanTurn::Persist(write) = stale.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected incremental persist");
        };
        assert_eq!(
            stale.on_write(write.operation(), WriteOutcome::Stale),
            PlanWriteOutcome::Stale
        );

        let mut cancelled_outcome = persistence_probe(Arc::clone(&accepted_writes));
        let PlanTurn::Persist(write) = cancelled_outcome.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected incremental persist");
        };
        assert_eq!(
            cancelled_outcome.on_write(write.operation(), WriteOutcome::Cancelled),
            PlanWriteOutcome::Cancelled(CancelReason::StoreRotated)
        );
        assert!(matches!(
            cancelled_outcome.persistence(),
            SessionPersistence::None
        ));

        let mut cancelled = persistence_probe(Arc::clone(&accepted_writes));
        let PlanTurn::Persist(write) = cancelled.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected incremental persist");
        };
        cancelled.cancel();
        assert_eq!(
            cancelled.on_write(write.operation(), WriteOutcome::Accepted),
            PlanWriteOutcome::Stale
        );
        assert_eq!(
            accepted_writes.load(std::sync::atomic::Ordering::Relaxed),
            0,
            "failed, stale, and cancelled writes must not release engine metadata"
        );

        let mut final_write = SessionPlan::new(budget());
        assert!(
            final_write.install_engine(Box::new(
                ScriptedEngine::new(
                    TreePlanId::new(2),
                    vec![ScriptedStep::Complete],
                    vec![PersistNode::new(
                        SHAMapHash::new(Uint256::from(100)),
                        Bytes::from_static(b"final-node"),
                        crate::io::StoredObjectKind::AccountNode,
                    )],
                )
                .with_persistence_sequence(1)
                .with_persistence_acceptance_counter(Arc::clone(&accepted_writes)),
            ))
        );
        let PlanTurn::Persist(write) = final_write.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected final persist");
        };
        assert!(
            write.fence().is_some(),
            "completed plans require a final fence"
        );
        assert_eq!(
            final_write.on_write(write.operation(), WriteOutcome::Accepted),
            PlanWriteOutcome::FinalAccepted
        );
        assert_eq!(
            accepted_writes.load(std::sync::atomic::Ordering::Relaxed),
            1,
            "only exact accepted writes notify the engine"
        );
    }

    #[test]
    fn mailbox_enforces_packet_and_byte_bounds() {
        let s = session();
        // A permissive gate budget: the mailbox itself enforces its caps.
        let budget = AdmissionBudget::new(16, 1024);
        // Byte cap.
        let mut mailbox = SessionMailbox::new(4, 100);
        assert!(mailbox.push(packet(s, budget, 30)));
        assert_eq!(mailbox.packet_count(), 1);
        assert_eq!(mailbox.packet_bytes(), 30);
        assert!(mailbox.push(packet(s, budget, 70)));
        assert_eq!(mailbox.packet_count(), 2);
        assert_eq!(mailbox.packet_bytes(), 100);
        // A byte-over-budget packet is dropped without mutation.
        assert!(!mailbox.push(packet(s, budget, 20)));
        assert_eq!(mailbox.packet_count(), 2);
        assert_eq!(mailbox.packet_bytes(), 100);
        mailbox.clear();
        assert!(mailbox.is_empty());
        assert_eq!(mailbox.packet_count(), 0);
        assert_eq!(mailbox.packet_bytes(), 0);

        // Packet cap (byte budget generous).
        let mut mailbox = SessionMailbox::new(4, 1024);
        for _ in 0..4 {
            assert!(mailbox.push(packet(s, budget, 4)));
        }
        assert_eq!(mailbox.packet_count(), 4);
        assert_eq!(mailbox.packet_bytes(), 4 * 4);
        // A packet-count-over-budget packet is dropped.
        assert!(!mailbox.push(packet(s, budget, 4)));
        assert_eq!(mailbox.packet_count(), 4);
        // Pop restores counts.
        assert!(mailbox.pop_front().is_some());
        assert_eq!(mailbox.packet_count(), 3);
        assert_eq!(mailbox.packet_bytes(), 3 * 4);
        mailbox.clear();
        assert!(mailbox.is_empty());
        assert_eq!(mailbox.packet_count(), 0);
        assert_eq!(mailbox.packet_bytes(), 0);
    }

    #[test]
    fn reads_are_deduped_and_match_the_exact_operation() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = scripted(1, vec![ScriptedStep::NeedsReads(vec![need(7), need(7)])]);
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        let PlanTurn::Reads(requests) = turn else {
            panic!("expected reads, got {turn:?}");
        };
        // The duplicate hash is announced once.
        assert_eq!(requests.len(), 1);
        let request = &requests[0];
        assert_eq!(request.key(), SHAMapHash::new(Uint256::from(7)));

        // A read with the wrong operation identity is stale.
        let wrong = OperationRef::new(
            s,
            OperationKind::Read,
            OperationId::new(99),
            OperationGeneration::new(1),
        );
        let stale = plan.on_read(&ReadCompletion::new(
            wrong,
            ReadOutcome::Settled { node: None },
        ));
        assert_eq!(stale, PlanReadOutcome::Stale);
        // The exact in-flight operation applies.
        let exact = plan.on_read(&ReadCompletion::new(
            request.operation(),
            ReadOutcome::Settled { node: None },
        ));
        assert_eq!(exact, PlanReadOutcome::Applied);
        // The applied read cannot apply again.
        let again = plan.on_read(&ReadCompletion::new(
            request.operation(),
            ReadOutcome::Settled { node: None },
        ));
        assert_eq!(again, PlanReadOutcome::Stale);
    }

    #[test]
    fn complete_after_apply_reaches_persistence_and_fences() {
        let mut ids = IdCounter::new();
        let s = session();
        // The plan cannot complete until its one read applies.
        let mut plan = scripted(
            1,
            vec![
                ScriptedStep::NeedsReads(vec![need(7)]),
                ScriptedStep::Complete,
            ],
        );
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        let PlanTurn::Reads(requests) = turn else {
            panic!("expected reads, got {turn:?}");
        };
        assert_eq!(requests.len(), 1);

        // Without the read the plan makes no further progress.
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        assert_eq!(turn, PlanTurn::Continue);

        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                requests[0].operation(),
                ReadOutcome::Settled { node: None },
            )),
            PlanReadOutcome::Applied
        );

        // The next turn completes and persists with an exact write+fence pair.
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        let PlanTurn::Persist(batch) = turn else {
            panic!("expected persist, got {turn:?}");
        };
        assert_eq!(batch.operation().kind(), OperationKind::Write);
        assert_eq!(
            batch.fence().expect("final batch fence").kind(),
            OperationKind::DurabilityFence
        );
        assert_eq!(
            plan.persistence(),
            &SessionPersistence::FinalWritePending {
                operation: batch.operation(),
                fence: batch.fence().expect("final batch fence"),
            }
        );

        // A fence completion before the write is stale.
        let stale = plan.on_durability(
            batch.fence().expect("final batch fence"),
            DurabilityOutcome::Passed,
        );
        assert_eq!(stale, PlanDurabilityOutcome::Stale);

        // The exact write acceptance arms the fence.
        let accepted = plan.on_write(batch.operation(), WriteOutcome::Accepted);
        assert_eq!(accepted, PlanWriteOutcome::FinalAccepted);
        assert_eq!(
            plan.persistence(),
            &SessionPersistence::FencePending {
                operation: batch.fence().expect("final batch fence"),
            }
        );

        // A wrong write operation is stale and cannot rearm the fence.
        let wrong_write = OperationRef::new(
            s,
            OperationKind::Write,
            OperationId::new(9),
            OperationGeneration::new(1),
        );
        assert_eq!(
            plan.on_write(wrong_write, WriteOutcome::Accepted),
            PlanWriteOutcome::Stale
        );
        assert_eq!(
            plan.persistence(),
            &SessionPersistence::FencePending {
                operation: batch.fence().expect("final batch fence"),
            }
        );

        // The passed fence makes the ledger durable.
        let durable = plan.on_durability(
            batch.fence().expect("final batch fence"),
            DurabilityOutcome::Passed,
        );
        assert_eq!(durable, PlanDurabilityOutcome::Durable);
        assert_eq!(plan.persistence(), &SessionPersistence::Durable);

        // No further work while persistence is committed.
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        assert_eq!(turn, PlanTurn::Continue);
    }

    #[test]
    fn write_and_fence_failures_terminalize_intent() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = scripted(1, vec![ScriptedStep::Complete]);
        let PlanTurn::Persist(batch) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected persist");
        };

        // A failed write leaves no durable intent.
        let failed = plan.on_write(batch.operation(), WriteOutcome::Failed);
        assert_eq!(
            failed,
            PlanWriteOutcome::Failed(FailureReason::WriteFailure)
        );
        assert_eq!(
            plan.persistence(),
            &SessionPersistence::Failed {
                reason: FailureReason::WriteFailure,
            }
        );

        let mut plan = scripted(1, vec![ScriptedStep::Complete]);
        let PlanTurn::Persist(batch) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected persist");
        };
        assert_eq!(
            plan.on_write(batch.operation(), WriteOutcome::Accepted),
            PlanWriteOutcome::FinalAccepted
        );
        let failed = plan.on_durability(
            batch.fence().expect("final batch fence"),
            DurabilityOutcome::Failed,
        );
        assert_eq!(
            failed,
            PlanDurabilityOutcome::Failed(FailureReason::DurabilityFenceFailed)
        );
        assert_eq!(
            plan.persistence(),
            &SessionPersistence::Failed {
                reason: FailureReason::DurabilityFenceFailed,
            }
        );
    }

    #[test]
    fn incremental_write_retains_discovered_reads_until_write_completion() {
        let mut ids = IdCounter::new();
        let s = session();
        let accepted_writes = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let mut plan = SessionPlan::new(budget());
        assert!(
            plan.install_engine(Box::new(
                ScriptedEngine::new(
                    TreePlanId::new(1),
                    vec![ScriptedStep::NeedsReads(vec![need(7)])],
                    vec![PersistNode::new(
                        SHAMapHash::new(Uint256::from(99)),
                        Bytes::from_static(b"accepted-node"),
                        crate::io::StoredObjectKind::AccountNode,
                    )],
                )
                .with_persistence_sequence(1)
                .with_persistence_acceptance_counter(Arc::clone(&accepted_writes)),
            ))
        );

        let PlanTurn::Persist(write) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected the accepted node to persist first");
        };
        assert!(write.fence().is_none(), "incremental writes have no fence");
        assert_eq!(plan.read_backlog_count(), 1, "read effect must be retained");
        assert_eq!(
            plan.pending_read_count(),
            0,
            "read dispatch waits for write ack"
        );

        assert_eq!(
            plan.on_write(write.operation(), WriteOutcome::Accepted),
            PlanWriteOutcome::IncrementalAccepted
        );
        assert_eq!(
            accepted_writes.load(std::sync::atomic::Ordering::Relaxed),
            1,
            "the engine is notified only after the exact write accepts"
        );
        let PlanTurn::Reads(reads) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected retained read after incremental write completion");
        };
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].key(), SHAMapHash::new(Uint256::from(7)));
    }

    #[test]
    fn incremental_write_retains_discovered_network_effect_until_write_completion() {
        let mut ids = IdCounter::new();
        let s = session();
        let network_need =
            PlanNetworkNeed::new(SHAMapNodeId::default(), Uint256::from(8), TreeKind::State);
        let mut plan = SessionPlan::new(budget());
        assert!(
            plan.install_engine(Box::new(
                ScriptedEngine::new(
                    TreePlanId::new(1),
                    vec![ScriptedStep::NeedsNetworkWithKind(vec![network_need])],
                    vec![PersistNode::new(
                        SHAMapHash::new(Uint256::from(100)),
                        Bytes::from_static(b"accepted-node"),
                        crate::io::StoredObjectKind::AccountNode,
                    )],
                )
                .with_persistence_sequence(1),
            ))
        );

        let PlanTurn::Persist(write) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected the accepted node to persist first");
        };
        assert_eq!(
            plan.on_write(write.operation(), WriteOutcome::Accepted),
            PlanWriteOutcome::IncrementalAccepted
        );
        let PlanTurn::Network(nodes) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected retained network effect after incremental write completion");
        };
        assert_eq!(nodes, vec![network_need]);
        assert!(plan.pending_network().contains(&Uint256::from(8)));
    }

    #[test]
    fn read_admission_backlog_is_fifo_and_bounded() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = SessionPlan::with_pending_reads_cap(budget(), 2);
        assert!(plan.install_engine(Box::new(ScriptedEngine::new(
            TreePlanId::new(1),
            vec![ScriptedStep::NeedsReads(vec![need(1), need(2), need(3)])],
            Vec::new(),
        ))));
        // Only two reads fit the cap; the last goes to the FIFO backlog.
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        let PlanTurn::Reads(requests) = turn else {
            panic!("expected reads");
        };
        assert_eq!(requests.len(), 2);
        assert_eq!(requests[0].key(), SHAMapHash::new(Uint256::from(1)));
        assert_eq!(requests[1].key(), SHAMapHash::new(Uint256::from(2)));

        // Nothing more is admitted while the cap is saturated.
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        assert_eq!(turn, PlanTurn::Continue);

        // The deferred-read barrier completes the whole admitted round before
        // sliding another backlog item into the bounded window.
        for request in &requests {
            assert_eq!(
                plan.on_read(&ReadCompletion::new(
                    request.operation(),
                    ReadOutcome::Settled { node: None },
                )),
                PlanReadOutcome::Applied
            );
        }
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        let PlanTurn::Reads(requests) = turn else {
            panic!("expected reads");
        };
        assert_eq!(requests.len(), 1);
        assert_eq!(requests[0].key(), SHAMapHash::new(Uint256::from(3)));
    }

    #[test]
    fn verified_local_read_attachment_counts_as_async_interval_progress() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = scripted(1, vec![ScriptedStep::NeedsReads(vec![need(7)])]);
        let PlanTurn::Reads(requests) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected a brokered local read");
        };
        assert!(
            plan.take_no_progress_interval(),
            "announcing a read is not verified data progress"
        );

        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                requests[0].operation(),
                ReadOutcome::Settled {
                    node: Some(Bytes::from_static(b"verified-local-node")),
                },
            )),
            PlanReadOutcome::Applied
        );
        assert!(
            !plan.take_no_progress_interval(),
            "a strongly attached local node must keep the async reconstruction alive"
        );
    }

    #[test]
    fn dormancy_rearms_real_tree_waiter_with_fresh_operation_identity() {
        let child = SHAMapTreeNode::new_leaf(
            shamap::tree_node::SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0x91; 32]), vec![0x91; 12]),
            0,
        );
        let child_hash = child.get_hash();
        let root = SHAMapTreeNode::new_inner(0);
        root.set_child_hash(0, child_hash);
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root,
            shamap::sync::SHAMapType::State,
            true,
            1,
            SyncState::Synching,
        );
        let engine = LedgerTreePlanEngine::new(TreePlan::new(
            TreePlanId::new(1),
            TreeKind::State,
            &tree,
            tree.root().get_hash(),
            256,
            1,
            &mut || 0,
        ));
        let mut plan = SessionPlan::new(budget());
        assert!(plan.install_engine(Box::new(engine)));
        let mut ids = IdCounter::new();
        let s = session();

        let PlanTurn::Reads(first) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected the initial retained-tree read");
        };
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].key(), child_hash);
        plan.suspend_for_dormancy();
        assert_eq!(plan.pending_read_count(), 0);

        let PlanTurn::Reads(replacement) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("reactivation must mint a replacement read for the retained edge");
        };
        assert_eq!(replacement.len(), 1);
        assert_eq!(replacement[0].key(), child_hash);
        assert_ne!(replacement[0].operation(), first[0].operation());
    }

    #[test]
    fn timeout_budget_allows_six_no_progress_recoveries_then_fails_on_seventh() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = SessionPlan::new(budget());
        assert_eq!(plan.on_timeout(true), PlanTimeout::Continue);
        assert_eq!(plan.on_timeout(false), PlanTimeout::Continue);
        assert_eq!(plan.timeouts(), 1, "progress consumes no timeout budget");
        for expected_timeouts in 2..=DEFAULT_MAX_ACQUIRE_TIMEOUTS {
            assert_eq!(plan.on_timeout(true), PlanTimeout::Continue);
            assert_eq!(plan.timeouts(), expected_timeouts);
        }
        assert_eq!(plan.on_timeout(true), PlanTimeout::Fail);
        assert!(plan.is_cancelled());
        // A cancelled plan produces no further work.
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        assert_eq!(turn, PlanTurn::Continue);
    }

    #[test]
    fn cancellation_clears_every_inflight_resource() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = scripted(
            1,
            vec![
                ScriptedStep::NeedsReads(vec![need(7)]),
                ScriptedStep::Complete,
            ],
        );
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        let PlanTurn::Reads(requests) = turn else {
            panic!("expected reads");
        };
        plan.cancel();
        assert!(plan.is_cancelled());
        assert!(plan.engine().is_none());
        assert_eq!(plan.packet_count(), 0);
        assert_eq!(plan.packet_bytes(), 0);
        assert!(plan.pending_network().is_empty());
        // Every late completion is stale after cancellation.
        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                requests[0].operation(),
                ReadOutcome::Settled { node: None }
            )),
            PlanReadOutcome::Stale
        );
        assert_eq!(plan.on_timeout(true), PlanTimeout::Fail);
    }

    #[test]
    fn network_candidates_are_tracked() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = scripted(
            1,
            vec![ScriptedStep::NeedsNetwork(vec![(
                SHAMapNodeId::default(),
                Uint256::from(42),
            )])],
        );
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        let PlanTurn::Network(nodes) = turn else {
            panic!("expected network, got {turn:?}");
        };
        assert_eq!(nodes.len(), 1);
        assert!(plan.pending_network().contains(&Uint256::from(42)));
        assert_eq!(nodes[0].kind(), TreeKind::State);
    }

    #[test]
    fn recovery_retirement_removes_an_unemitted_exact_network_need() {
        let mut ids = IdCounter::new();
        let s = session();
        let nodes = [
            PlanNetworkNeed::new(SHAMapNodeId::default(), Uint256::from(1), TreeKind::State),
            PlanNetworkNeed::new(SHAMapNodeId::default(), Uint256::from(2), TreeKind::State),
            PlanNetworkNeed::new(SHAMapNodeId::default(), Uint256::from(3), TreeKind::State),
        ];
        let mut plan = SessionPlan::new(budget());
        assert!(
            plan.install_engine(Box::new(
                ScriptedEngine::new(
                    TreePlanId::new(1),
                    vec![ScriptedStep::NeedsNetworkWithKind(nodes.to_vec())],
                    Vec::new(),
                )
                .with_persistence_sequence(1),
            ))
        );

        let PlanTurn::Network(dispatched) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected retained network frontier");
        };
        assert_eq!(dispatched, nodes.to_vec());
        assert_eq!(plan.take_next_normal_network_batch(1), vec![nodes[0]]);

        // The second record is still retained but has not been serialized. A
        // matching recovery attachment retires that exact record, including
        // its normal-emission FIFO entry, without touching the third need.
        let recovery = plan.reprobe_network_batch(&[nodes[1]], &mut ctx(s, &mut ids));
        assert_eq!(recovery.len(), 1);
        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                recovery[0].operation(),
                ReadOutcome::Settled {
                    node: Some(Bytes::from_static(b"resolved")),
                },
            )),
            PlanReadOutcome::Applied
        );
        assert_eq!(plan.take_next_normal_network_batch(12), vec![nodes[2]]);
        assert!(
            !plan.pending_network().contains(&nodes[1].hash()),
            "an exact recovery attachment must retire its unsent normal record"
        );
    }

    #[test]
    fn frontier_overflow_is_backlogged_without_dropping_and_exact_retirement_updates_status() {
        let mut ids = IdCounter::new();
        let s = session();
        let nodes = (1..=u64::try_from(MAX_RETAINED_NETWORK_FRONTIER + 2).expect("cap fits"))
            .map(|hash| {
                PlanNetworkNeed::new(
                    SHAMapNodeId::default(),
                    Uint256::from(hash),
                    TreeKind::State,
                )
            })
            .collect::<Vec<_>>();
        let mut plan = SessionPlan::new(budget());
        plan.enqueue_network_frontier(nodes.clone());
        let dispatched = plan.dispatch_network_backlog();
        assert_eq!(dispatched.len(), MAX_RETAINED_NETWORK_FRONTIER);
        assert_eq!(plan.retained_network().len(), MAX_RETAINED_NETWORK_FRONTIER);
        assert_eq!(
            plan.pending_network().len(),
            MAX_RETAINED_NETWORK_FRONTIER + 2
        );

        // A matching attachment retires only that exact retained entry and
        // causes the next turn to dispatch one preserved overflow need.
        plan.retire_network_resolutions(&[nodes[0]]);
        assert!(!plan.pending_network().contains(&nodes[0].hash()));
        assert_eq!(
            plan.retained_network().len(),
            MAX_RETAINED_NETWORK_FRONTIER - 1
        );
        let PlanTurn::Network(next) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("freed retained capacity must dispatch queued frontier work");
        };
        assert_eq!(next, vec![nodes[MAX_RETAINED_NETWORK_FRONTIER]]);
        assert_eq!(plan.retained_network().len(), MAX_RETAINED_NETWORK_FRONTIER);
        assert!(
            plan.pending_network()
                .contains(&nodes[MAX_RETAINED_NETWORK_FRONTIER].hash())
        );
    }

    #[test]
    fn timeout_recovery_retains_and_rotates_the_complete_bounded_frontier() {
        let mut ids = IdCounter::new();
        let s = session();
        let frontier_len = u64::try_from(MAX_RETAINED_NETWORK_FRONTIER - 4)
            .expect("bounded frontier cap fits in u64");
        let mut announced = (1..=frontier_len)
            .map(|hash| {
                PlanNetworkNeed::new(
                    SHAMapNodeId::default(),
                    Uint256::from(hash),
                    TreeKind::Transaction,
                )
            })
            .collect::<Vec<_>>();
        // TreePlan normally emits unique needs; retain the same invariant even
        // if a boundary fake or adapter repeats an exact entry.
        announced.push(announced[0]);
        let needs = announced[..MAX_RETAINED_NETWORK_FRONTIER - 4].to_vec();
        let mut plan = scripted(1, vec![ScriptedStep::NeedsNetworkWithKind(announced)]);
        let PlanTurn::Network(nodes) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected network turn");
        };
        assert_eq!(nodes.len(), MAX_RETAINED_NETWORK_FRONTIER - 4);
        assert_eq!(plan.retained_network(), needs.as_slice());
        assert_eq!(
            plan.retained_network().len(),
            MAX_RETAINED_NETWORK_FRONTIER - 4
        );

        // One no-progress timeout selects one exact batch. The coordinator
        // passes this same batch to both the brokered local reprobe and peer
        // resend paths, so later retained entries cannot remain unreachable.
        let first_batch = plan.next_timeout_recovery_batch();
        assert_eq!(first_batch, needs[..MAX_TIMEOUT_REPROBES].to_vec());
        let first_reads = plan.reprobe_network_batch(&first_batch, &mut ctx(s, &mut ids));
        assert_eq!(first_reads.len(), MAX_TIMEOUT_REPROBES);
        assert_eq!(
            first_reads.iter().map(ReadRequest::key).collect::<Vec<_>>(),
            first_batch
                .iter()
                .map(|need| SHAMapHash::new(need.hash()))
                .collect::<Vec<_>>()
        );

        let second_batch = plan.next_timeout_recovery_batch();
        assert_eq!(second_batch, needs[MAX_TIMEOUT_REPROBES..24].to_vec());
        let second_reads = plan.reprobe_network_batch(&second_batch, &mut ctx(s, &mut ids));
        assert_eq!(second_reads.len(), MAX_TIMEOUT_REPROBES);
        assert_eq!(
            second_reads
                .iter()
                .map(ReadRequest::key)
                .collect::<Vec<_>>(),
            second_batch
                .iter()
                .map(|need| SHAMapHash::new(need.hash()))
                .collect::<Vec<_>>()
        );

        // The observed 252-entry frontier eventually reaches its final batch,
        // then wraps to the first; repeated timeouts cannot pin it behind the
        // initial twelve entries.
        let final_batch_start = ((needs.len() - 1) / MAX_TIMEOUT_REPROBES) * MAX_TIMEOUT_REPROBES;
        for _ in 0..(final_batch_start / MAX_TIMEOUT_REPROBES - 2) {
            let _ = plan.next_timeout_recovery_batch();
        }
        let expected_wrapped = (0..MAX_TIMEOUT_REPROBES)
            .map(|offset| needs[(final_batch_start + offset) % needs.len()])
            .collect::<Vec<_>>();
        assert_eq!(plan.next_timeout_recovery_batch(), expected_wrapped);
        let next_start = (final_batch_start + MAX_TIMEOUT_REPROBES) % needs.len();
        let expected_next = (0..MAX_TIMEOUT_REPROBES)
            .map(|offset| needs[(next_start + offset) % needs.len()])
            .collect::<Vec<_>>();
        assert_eq!(plan.next_timeout_recovery_batch(), expected_next);
    }

    #[test]
    fn timeout_scan_republishes_a_recent_edge_hidden_after_a_partial_reply() {
        let mut ids = IdCounter::new();
        let s = session();
        let need = PlanNetworkNeed::new(
            SHAMapNodeId::default(),
            Uint256::from(0x77),
            TreeKind::State,
        );
        let mut plan = scripted(
            1,
            vec![
                ScriptedStep::NeedsNetworkWithKind(vec![need]),
                // A fresh SHAMap reply/timeout scan sees the same still-missing
                // edge again.
                ScriptedStep::NeedsNetworkWithKind(vec![need]),
            ],
        );

        let PlanTurn::Network(_) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected initial network frontier");
        };
        assert_eq!(plan.take_next_normal_network_batch(1), vec![need]);

        // A useful partial reply starts a new scan and clears the actor-side
        // epoch. Its unanswered sibling remains owned by the SHAMap plan, but
        // was recently requested and therefore was not re-published.
        plan.reset_network_epoch();
        assert!(plan.pending_network().is_empty());

        plan.begin_timeout_scan(vec![PeerId::new(1)], std::iter::empty());
        let PlanTurn::Network(republished) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("timeout must rebuild the hidden SHAMap frontier");
        };
        assert_eq!(republished, vec![need]);
        assert_eq!(plan.pending_network(), &BTreeSet::from([need.hash()]));
    }

    #[test]
    fn retained_network_frontier_merges_incremental_batches_by_exact_need() {
        let first =
            PlanNetworkNeed::new(SHAMapNodeId::default(), Uint256::from(1), TreeKind::State);
        let same_hash_other_kind = PlanNetworkNeed::new(
            SHAMapNodeId::default(),
            Uint256::from(1),
            TreeKind::Transaction,
        );
        let second =
            PlanNetworkNeed::new(SHAMapNodeId::default(), Uint256::from(2), TreeKind::State);
        let mut plan = SessionPlan::new(budget());
        plan.enqueue_network_frontier([first, same_hash_other_kind]);
        assert_eq!(
            plan.dispatch_network_backlog(),
            vec![first, same_hash_other_kind]
        );
        let _ = plan.next_timeout_recovery_batch();
        plan.enqueue_network_frontier([first, second]);
        assert_eq!(plan.dispatch_network_backlog(), vec![second]);

        assert_eq!(
            plan.retained_network(),
            &[first, same_hash_other_kind, second],
            "an incremental batch merges instead of superseding still-blocked needs"
        );
        assert_eq!(
            plan.next_timeout_recovery_batch(),
            vec![first, same_hash_other_kind, second],
            "merging does not reset the rotating timeout cursor"
        );
    }

    #[test]
    fn timeout_recovery_read_is_exact_and_retires_only_a_verified_attachment() {
        let mut ids = IdCounter::new();
        let s = session();
        let need = PlanNetworkNeed::new(
            SHAMapNodeId::default(),
            Uint256::from(0x77),
            TreeKind::State,
        );
        let mut plan = scripted(1, vec![ScriptedStep::NeedsNetworkWithKind(vec![need])]);
        let PlanTurn::Network(_) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected retained network need");
        };

        let first = plan.reprobe_network_batch(&[need], &mut ctx(s, &mut ids));
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].operation().kind(), OperationKind::RecoveryRead);
        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                first[0].operation(),
                ReadOutcome::Settled { node: None },
            )),
            PlanReadOutcome::Applied
        );
        assert_eq!(
            plan.retained_network(),
            &[need],
            "a miss does not retire recovery state"
        );

        let second = plan.reprobe_network_batch(&[need], &mut ctx(s, &mut ids));
        assert_eq!(second.len(), 1);
        assert_ne!(second[0].operation(), first[0].operation());
        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                first[0].operation(),
                ReadOutcome::Settled {
                    node: Some(Bytes::from_static(b"late")),
                },
            )),
            PlanReadOutcome::Stale,
            "a late same-kind recovery completion cannot attach after rearm"
        );
        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                second[0].operation(),
                ReadOutcome::Settled {
                    node: Some(Bytes::from_static(b"prefix-form-node")),
                },
            )),
            PlanReadOutcome::Applied
        );
        assert!(
            plan.retained_network().is_empty(),
            "only the verified exact hit retires it"
        );

        let third_need = PlanNetworkNeed::new(
            SHAMapNodeId::default(),
            Uint256::from(0x78),
            TreeKind::State,
        );
        plan.enqueue_network_frontier([third_need]);
        assert_eq!(plan.dispatch_network_backlog(), vec![third_need]);
        let third = plan.reprobe_network_batch(&[third_need], &mut ctx(s, &mut ids));
        plan.cancel();
        assert_eq!(
            plan.on_read(&ReadCompletion::new(
                third[0].operation(),
                ReadOutcome::Settled {
                    node: Some(Bytes::from_static(b"cancelled")),
                },
            )),
            PlanReadOutcome::Stale,
            "cancellation invalidates the exact recovery operation immediately"
        );
    }

    #[test]
    fn scripted_network_need_preserves_transaction_kind() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = scripted(
            1,
            vec![ScriptedStep::NeedsNetworkWithKind(vec![
                PlanNetworkNeed::new(
                    SHAMapNodeId::default(),
                    Uint256::from(77),
                    TreeKind::Transaction,
                ),
            ])],
        );
        let PlanTurn::Network(nodes) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected network turn");
        };
        assert_eq!(nodes[0].hash(), Uint256::from(77));
        assert_eq!(nodes[0].kind(), TreeKind::Transaction);
    }

    #[test]
    fn invalid_plan_is_surfaced_as_invalid_turn() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = scripted(1, vec![ScriptedStep::Invalid]);
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        assert_eq!(turn, PlanTurn::Invalid);
    }

    #[test]
    fn packets_are_fed_into_the_engine_in_bounded_batches() {
        let mut ids = IdCounter::new();
        let s = session();
        let mut plan = SessionPlan::new(budget());
        assert!(plan.install_engine(Box::new(ScriptedEngine::new(
            TreePlanId::new(1),
            Vec::new(),
            Vec::new(),
        ))));
        // Feed six packets; only the bounded per-turn batch is consumed.
        for _ in 0..6 {
            assert!(plan.push_packet(packet(s, AdmissionBudget::new(1, 64), 8)));
        }
        assert_eq!(plan.packet_count(), 6);
        let turn = plan.run_turn(&mut ctx(s, &mut ids));
        assert_eq!(turn, PlanTurn::Continue);
        assert_eq!(plan.packet_count(), 2);
    }

    #[test]
    fn install_engine_is_single_shot() {
        let mut plan = SessionPlan::new(budget());
        assert!(plan.install_engine(Box::new(ScriptedEngine::new(
            TreePlanId::new(1),
            Vec::new(),
            Vec::new(),
        ))));
        assert!(!plan.install_engine(Box::new(ScriptedEngine::new(
            TreePlanId::new(2),
            Vec::new(),
            Vec::new(),
        ))));
        assert_eq!(plan.engine().expect("engine").plan_id(), TreePlanId::new(1));
    }

    #[test]
    fn retained_network_frontier_caps_at_rippled_scan_bound_and_preserves_overflow_backlog() {
        let mut ids = IdCounter::new();
        let s = session();
        let needs = (0..(MAX_RETAINED_NETWORK_FRONTIER + 1))
            .map(|index| {
                PlanNetworkNeed::new(
                    SHAMapNodeId::default(),
                    Uint256::from((index + 1) as u64),
                    TreeKind::State,
                )
            })
            .collect::<Vec<_>>();
        let overflow = *needs.last().expect("one exact overflow need");
        let mut plan = scripted(1, vec![ScriptedStep::NeedsNetworkWithKind(needs)]);

        let PlanTurn::Network(dispatched) = plan.run_turn(&mut ctx(s, &mut ids)) else {
            panic!("expected retained network frontier dispatch");
        };
        assert_eq!(MAX_RETAINED_NETWORK_FRONTIER, 768);
        assert_eq!(dispatched.len(), MAX_RETAINED_NETWORK_FRONTIER);
        assert_eq!(plan.retained_network().len(), MAX_RETAINED_NETWORK_FRONTIER);
        assert_eq!(plan.network_backlog.len(), 1);
        assert_eq!(plan.network_backlog.front(), Some(&overflow));
        assert_eq!(
            plan.pending_network().len(),
            MAX_RETAINED_NETWORK_FRONTIER + 1
        );
        assert!(
            plan.pending_network().contains(&overflow.hash()),
            "the exact overflow need remains visible and retryable"
        );
    }

    #[test]
    fn real_engine_traverses_a_rooted_tree_fixture() {
        // A rooted two-level state tree with one missing child, exercised with
        // the real ledger TreePlan over NullResident (no synchronous reads).
        // The child is a real leaf node whose hash we compute first, then hang
        // under the root by its hash, so a decoded copy of the child can be
        // applied back and matches exactly.
        let child = SHAMapTreeNode::new_leaf(
            shamap::tree_node::SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from(1), vec![0u8; 12]),
            0,
        );
        let child_hash = child.get_hash();
        assert!(!child_hash.is_zero());

        let root = SHAMapTreeNode::new_inner(0);
        root.set_child_hash(1, child_hash);
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root,
            shamap::sync::SHAMapType::State,
            true,
            1,
            SyncState::Synching,
        );

        let mut engine = LedgerTreePlanEngine::new(TreePlan::new(
            TreePlanId::new(1),
            TreeKind::State,
            &tree,
            child_hash,
            256,
            // Non-zero full-below generation so the fresh root (generation 0)
            // is not treated as fully below and is scanned for missing nodes.
            1,
            &mut || rand_int_to(255u8),
        ));
        assert_eq!(engine.plan_id(), TreePlanId::new(1));

        // The traversal announces the missing child subtree as a read.
        match engine.advance(MAX_NEW_READS_PER_PASS) {
            PlanStepOutcome::NeedsReads(reads) => {
                assert_eq!(reads.len(), 1);
                assert_eq!(reads[0].hash(), child_hash);
            }
            other => panic!("expected a read need, got {other:?}"),
        }

        // A decoded wire copy of the child attaches through the announced
        // read path (the coordinator's NodeStore broker would deliver it).
        let serialized = child.serialize_for_wire().expect("serialize child");
        match engine.apply_read(
            child_hash,
            &ReadOutcome::Settled {
                node: Some(Bytes::from(serialized)),
            },
        ) {
            PlanReadApply::Applied { .. } | PlanReadApply::HashMismatch => {}
            other => panic!("unexpected apply {other:?}"),
        }

        // The plan may now complete or wait on the scheduler; either is a
        // legal bounded outcome. The key invariant is the traversal boundary
        // held: reads were announced, no synchronous I/O occurred.
        let outcome = engine.advance(MAX_NEW_READS_PER_PASS);
        assert!(
            matches!(outcome, PlanStepOutcome::Ready | PlanStepOutcome::Complete),
            "unexpected outcome {outcome:?}"
        );
    }
}
