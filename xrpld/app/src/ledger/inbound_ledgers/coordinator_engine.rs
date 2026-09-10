//! App-side composite [`TreeEngine`] and [`PlanSeed`] for the M4.2
//! coordinator switchover.
//!
//! The acquisition coordinator drives exactly one [`TreeEngine`] per session.
//! Rippled acquires the state tree and the transaction tree as one unit, so
//! this engine sequences the State plan and the Transaction plan internally
//! and reports `PlanStepOutcome::Complete` only when the whole ledger is
//! structurally complete (`InboundLedgerLocal::is_complete`).
//!
//! Ownership boundary: the engine is the unique owner of the per-acquisition
//! app resources that packet admission mutates (`InboundLedgerLocal`,
//! `WorkerStore`, `WorkerFetchPack`) plus Arc clones of the shared tree cache
//! and full-below cache used by the resident lookup. It exposes none of them
//! to the coordinator; the coordinator sees only the [`TreeEngine`] trait.
//! This keeps `xrpld/acquisition` free of app dependencies while preserving the
//! exact packet-admission path the actor uses.

use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};

use basics::base_uint::Uint256;
use basics::hardened_hash::HardenedHashBuilder;
use basics::intrusive_pointer::SharedIntrusive;
use basics::random::rand_int_to;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::MonotonicClock;
use bytes::Bytes;
use ledger::{
    FetchPackCache, InboundLedgerDataType, InboundLedgerLocal, InboundLedgerNodeData,
    InboundLedgerPacket, InboundLedgerReason, LedgerConfig, TreeAdvance, TreeKind, TreePlan,
    TreePlanId,
};
use shamap::family::{FullBelowCache, FullBelowCacheImpl, NullMissingNodeReporter, SHAMapFamily};
use shamap::node_id::deserialize_shamap_node_id;
use shamap::sync::{MissingNodeReadApply, MissingNodeReadOutcome, MissingNodeResidentLookup};
use shamap::tree_node::SHAMapTreeNode;
use shamap::tree_node_cache::TreeNodeCache;

use acquisition::{
    PersistNode, PlanNetworkApply, PlanNetworkNeed, PlanReadApply, PlanReadNeed, PlanSeed,
    PlanStepOutcome, ReadOutcome, SessionRef, TreeEngine,
};

use super::acquisition::{ActorNodeFetcher, WorkerFetchPack, WorkerJournal, WorkerStore};

/// The concrete acquisition family for the app: shared tree cache + full-below
/// cache, a fetcher that never performs synchronous NodeStore I/O, and no
/// missing-node reporter. Matches `SHAMapFamily::new` used by the actor.
///
/// Not yet referenced outside this module; wired into the coordinator adapter
/// in sub-slice M4.2-B.
#[allow(dead_code)]
type AppFamily = SHAMapFamily<
    MonotonicClock,
    HardenedHashBuilder,
    Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    ActorNodeFetcher,
    NullMissingNodeReporter,
    (),
>;

/// Resident lookup over the shared caches and the fetch-pack, matching the
/// actor's `ActorResident` semantics plus rippled `checkLocal`'s by-hash
/// fetch-pack resolution. `is_full_below`/`mark_full_below` are retained so an
/// already-full subtree is not rescanned.
#[allow(dead_code)] // constructed by `AppLedgerPlanEngine::advance` in M4.2-B
struct AppResident<'a> {
    cache: &'a TreeNodeCache<MonotonicClock>,
    shared_full_below: &'a FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>,
    pending_full_below: &'a mut BTreeMap<Uint256, (SharedIntrusive<SHAMapTreeNode>, u32)>,
    fetch_pack: &'a FetchPackCache,
    store: &'a mut WorkerStore,
    kind: TreeKind,
}

impl MissingNodeResidentLookup for AppResident<'_> {
    fn load_resident(
        &mut self,
        hash: SHAMapHash,
        ledger_seq: u32,
    ) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        if let Some(node) = self.cache.fetch(hash.as_uint256()) {
            return self
                .store
                .store_resident_shamap_node(self.kind, &node, ledger_seq)
                .then_some(node);
        }
        // A fetch-pack entry is by-hash node data stored in the prefixed form
        // rippled's `addFetchPack` produces, the exact resident form the
        // traversal may resolve without a NodeStore read or a peer reply
        // (`gotFetchPack` -> `checkLocal` parity). Decode on each lookup:
        // fetch-pack passes are infrequent and the fetch caches stay bounded.
        let blob = self.fetch_pack.get_fetch_pack(*hash.as_uint256())?;
        let mut node = SHAMapTreeNode::make_from_prefix(&blob, hash).ok()?;
        self.cache
            .canonicalize_replace_client(hash.as_uint256(), &mut node);
        self.store
            .store_resident_shamap_node(self.kind, &node, ledger_seq)
            .then_some(node)
    }

    fn is_full_below(&mut self, hash: SHAMapHash) -> bool {
        self.shared_full_below.touch_if_exists(*hash.as_uint256())
    }

    fn mark_full_below(&mut self, node: SharedIntrusive<SHAMapTreeNode>, generation: u32) {
        // A FullBelow marker is a cross-session assertion: another traversal
        // may skip the entire subtree before checking the node cache. Cache and
        // fetch-pack hits are conservatively queued for persistence, so their
        // markers wait for the asynchronous WorkerStore durability barrier.
        // Direct NodeStore reads enqueue no write and publish immediately;
        // otherwise an all-NodeStore traversal has no completion to release its
        // reusable FullBelow discoveries.
        let hash = *node.get_hash().as_uint256();
        if self.store.has_pending_write_nodes() {
            self.pending_full_below.insert(hash, (node, generation));
        } else {
            node.set_full_below_gen(generation);
            self.shared_full_below.insert(hash);
        }
    }
}

/// Composite engine that acquires the state tree and then the transaction tree
/// of one `InboundLedgerLocal`, retaining exactly one `TreePlan` at a time.
pub(crate) struct AppLedgerPlanEngine {
    session: SessionRef,
    plan_id: TreePlanId,
    inbound: InboundLedgerLocal,
    store: WorkerStore,
    fetch_pack: WorkerFetchPack,
    family: AppFamily,
    cache: Arc<TreeNodeCache<MonotonicClock>>,
    full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    active_kind: Option<TreeKind>,
    active_plan: Option<TreePlan>,
    pending_full_below: BTreeMap<Uint256, (SharedIntrusive<SHAMapTreeNode>, u32)>,
    cached_root_steps: u64,
    idle_ready_logged: bool,
}

impl std::fmt::Debug for AppLedgerPlanEngine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppLedgerPlanEngine")
            .field("plan_id", &self.plan_id)
            .field("active_kind", &self.active_kind)
            .field("complete", &self.inbound.is_complete())
            .field("failed", &self.inbound.is_failed())
            .finish()
    }
}

#[allow(dead_code)] // wired in sub-slice M4.2-B
impl AppLedgerPlanEngine {
    pub(crate) fn new(
        session: SessionRef,
        plan_id: TreePlanId,
        inbound: InboundLedgerLocal,
        store: WorkerStore,
        fetch_pack: WorkerFetchPack,
        family: AppFamily,
        cache: Arc<TreeNodeCache<MonotonicClock>>,
        full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    ) -> Self {
        Self {
            session,
            plan_id,
            inbound,
            store,
            fetch_pack,
            family,
            cache,
            full_below,
            active_kind: None,
            active_plan: None,
            pending_full_below: BTreeMap::new(),
            cached_root_steps: 0,
            idle_ready_logged: false,
        }
    }

    /// Emits one causal record when traversal reports `Ready` but has no
    /// runnable frontier. This is the terminally relevant no-effect decision
    /// between an accepted incremental write and a read/network request.
    fn trace_idle_ready(&mut self) {
        if self.idle_ready_logged {
            return;
        }
        self.idle_ready_logged = true;
        let state = self.inbound.planner_state();
        let (state_map_hash, state_root_hash, tx_map_hash, tx_root_hash) = self
            .inbound
            .ledger_mut()
            .map(|ledger| {
                (
                    ledger.state_map_mut().hash(),
                    ledger.header().account_hash,
                    ledger.tx_map_mut().hash(),
                    ledger.header().tx_hash,
                )
            })
            .unwrap_or_default();
        let (
            active_kind,
            runnable,
            branch_steps,
            pending_hashes,
            pending_edges,
            pending_edge_bytes,
        ) = self
            .active_plan
            .as_ref()
            .map(|plan| {
                (
                    self.active_kind,
                    plan.has_runnable_frontier(),
                    plan.branch_steps(),
                    plan.pending_hashes(),
                    plan.pending_edges(),
                    plan.pending_edge_bytes(),
                )
            })
            .unwrap_or((None, false, 0, 0, 0, 0));
        tracing::info!(
            target: "acquisition_trace",
            event = "planner_ready_without_work",
            run_epoch = self.session.run_epoch().get(),
            session_id = self.session.session_id().get(),
            target_hash = %self.session.target_hash(),
            plan_epoch = self.session.plan_epoch().get(),
            store_generation = self.session.store_generation().get(),
            active_kind = ?active_kind,
            have_header = state.have_header,
            have_state = state.have_state,
            have_transactions = state.have_transactions,
            state_map_hash = %state_map_hash,
            state_root_hash = %state_root_hash,
            transaction_map_hash = %tx_map_hash,
            transaction_root_hash = %tx_root_hash,
            runnable,
            branch_steps,
            pending_hashes,
            pending_edges,
            pending_edge_bytes,
            treenode_cache_entries = self.cache.get_cache_size(),
            full_below_cache_entries = self.full_below.size(),
            "acquisition trace: planner returned Ready without a runnable SHAMap frontier"
        );
    }

    /// Moves staged full-below discoveries into the shared cache only after
    /// their associated NodeStore batch was accepted. This preserves rippled's
    /// store-before-shared-completion ordering across Quaxar's async write port.
    fn publish_persisted_full_below(&mut self) {
        let markers = std::mem::take(&mut self.pending_full_below);
        if markers.is_empty() {
            return;
        }
        let marker_count = markers.len();
        for (hash, (node, generation)) in markers {
            node.set_full_below_gen(generation);
            self.full_below.insert(hash);
        }
        tracing::info!(
            target: "acquisition_trace",
            event = "full_below_published_after_write",
            run_epoch = self.session.run_epoch().get(),
            session_id = self.session.session_id().get(),
            target_hash = %self.session.target_hash(),
            plan_epoch = self.session.plan_epoch().get(),
            store_generation = self.session.store_generation().get(),
            marker_count,
            shared_full_below_entries = self.full_below.size(),
            "acquisition trace: persistence-qualified SHAMap full-below markers published"
        );
    }

    /// The next tree that still needs acquisition, in rippled order: state
    /// before transactions.
    fn next_tree_kind(&self) -> Option<TreeKind> {
        let state = self.inbound.planner_state();
        if !state.have_state {
            return Some(TreeKind::State);
        }
        if !state.have_transactions {
            return Some(TreeKind::Transaction);
        }
        None
    }

    /// Mirrors `InboundLedgerLocal::prepare_trigger` (ledger_fetcher.rs:3175):
    /// a plan is started only after the tree's root node is present. Before
    /// that, the root node is announced over the network; the header applied an
    /// empty map whose root hash is zero.
    fn missing_root_node(
        &mut self,
        kind: TreeKind,
    ) -> Option<(shamap::node_id::SHAMapNodeId, Uint256)> {
        let ledger = self.inbound.ledger_mut()?;
        let (map_hash, root_hash) = match kind {
            TreeKind::State => (ledger.state_map_mut().hash(), ledger.header().account_hash),
            TreeKind::Transaction => (ledger.tx_map_mut().hash(), ledger.header().tx_hash),
        };
        if !map_hash.is_zero() {
            return None;
        }
        (!root_hash.is_zero()).then(|| {
            (
                shamap::node_id::SHAMapNodeId::default(),
                *root_hash.as_uint256(),
            )
        })
    }

    /// Applies a cached by-hash root through the ordinary packet path. Generic
    /// `TMGetObjectByHash` replies are cached, not routed as `TMLedgerData`,
    /// so a tree with no installed root must consume its matching fetch-pack
    /// entry before it can start a `TreePlan`. Rippled reaches the equivalent
    /// `checkLocal` path from `InboundLedgersImp::gotFetchPack()`.
    fn apply_cached_root(
        &mut self,
        kind: TreeKind,
        node_id: shamap::node_id::SHAMapNodeId,
        hash: Uint256,
    ) -> bool {
        // A replacement session shares the process-wide TreeNodeCache with
        // its predecessor. Consult it before issuing another root request;
        // otherwise a cancelled acquisition can leave an almost-complete
        // durable tree resident while every replacement still starts from a
        // network root round trip. FetchPack remains the encoded fallback.
        let node = if let Some(node) = self.cache.fetch(&hash) {
            node
        } else {
            let Some(blob) = self.fetch_pack.cache().get_fetch_pack(hash) else {
                return false;
            };
            let Ok(node) = SHAMapTreeNode::make_from_prefix(&blob, SHAMapHash::new(hash)) else {
                return false;
            };
            node
        };
        if *node.get_hash().as_uint256() != hash {
            return false;
        }
        let Ok(node_data) = node.serialize_for_wire() else {
            return false;
        };
        let packet = InboundLedgerPacket::new(
            match kind {
                TreeKind::State => InboundLedgerDataType::StateNode,
                TreeKind::Transaction => InboundLedgerDataType::TransactionNode,
            },
            vec![InboundLedgerNodeData::new(
                Some(node_id.get_raw_string()),
                node_data,
            )],
        );
        let journal = WorkerJournal;
        let config = LedgerConfig::default();
        self.inbound
            .process_packet_with_family_and_config(
                &packet,
                &journal,
                &config,
                &mut self.store,
                &mut self.fetch_pack,
                &self.family,
            )
            .is_ok_and(|stats| !stats.is_invalid())
    }

    /// Drains accepted filter writes once per coordinator turn. The worker
    /// store only collects commands; physical NuDB I/O remains outside this
    /// engine through the coordinator write port.
    fn take_accepted_writes(&mut self) -> Vec<PersistNode> {
        self.store.take_pending_write_nodes()
    }

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

impl TreeEngine for AppLedgerPlanEngine {
    fn plan_id(&self) -> TreePlanId {
        self.plan_id
    }

    fn advance(&mut self, max_new_reads: usize) -> PlanStepOutcome {
        loop {
            if self.inbound.is_failed() {
                return PlanStepOutcome::Invalid;
            }
            if self.inbound.is_complete() {
                return PlanStepOutcome::Complete;
            }
            if self.active_plan.is_none() {
                let Some(kind) = self.next_tree_kind() else {
                    return PlanStepOutcome::Complete;
                };
                if let Some((node_id, hash)) = self.missing_root_node(kind) {
                    // A generic by-hash reply may already have supplied this
                    // root to the shared fetch-pack cache. Install it before
                    // reissuing the same request; otherwise root-only cache
                    // progress can never make the tree plan runnable.
                    if self.apply_cached_root(kind, node_id, hash) {
                        self.cached_root_steps += 1;
                        continue;
                    }
                    // The root has not been applied or cached yet: announce it
                    // over the network exactly like `prepare_trigger`'s
                    // root-node request instead of planning over an empty map.
                    return PlanStepOutcome::NeedsNetwork(vec![PlanNetworkNeed::new(
                        node_id, hash, kind,
                    )]);
                }
                let Some(plan) =
                    self.inbound
                        .start_tree_plan(kind, self.plan_id, self.full_below.generation())
                else {
                    if self.inbound.is_failed() {
                        return PlanStepOutcome::Invalid;
                    }
                    return PlanStepOutcome::Complete;
                };
                self.active_kind = Some(kind);
                self.active_plan = Some(plan);
            }

            let mut resident = AppResident {
                cache: &self.cache,
                shared_full_below: &self.full_below,
                pending_full_below: &mut self.pending_full_below,
                fetch_pack: self.fetch_pack.cache(),
                store: &mut self.store,
                kind: self.active_kind.expect("active tree kind set"),
            };
            let mut first_child = || rand_int_to(255u8);
            let mut yield_now = || false;
            let advance = {
                let plan = self.active_plan.as_mut().expect("active plan set");
                plan.advance_with_yield(
                    max_new_reads,
                    &mut resident,
                    &mut first_child,
                    &mut yield_now,
                )
            };
            match advance {
                TreeAdvance::Ready => {
                    if !self.has_runnable_frontier() {
                        self.trace_idle_ready();
                    }
                    return PlanStepOutcome::Ready;
                }
                TreeAdvance::NeedsReads(reads) => {
                    return PlanStepOutcome::NeedsReads(
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
                    );
                }
                TreeAdvance::NeedsNetwork(nodes) => {
                    let kind = self.active_kind.expect("active tree kind set");
                    return PlanStepOutcome::NeedsNetwork(
                        nodes
                            .into_iter()
                            .map(|(node_id, hash)| PlanNetworkNeed::new(node_id, hash, kind))
                            .collect(),
                    );
                }
                TreeAdvance::Complete => {
                    let kind = self.active_kind.take().expect("active kind set");
                    self.active_plan = None;
                    if !self.inbound.complete_tree_plan(kind) {
                        return PlanStepOutcome::Invalid;
                    }
                    continue;
                }
                TreeAdvance::Invalid => return PlanStepOutcome::Invalid,
            }
        }
    }

    fn apply_read(&mut self, hash: SHAMapHash, outcome: &ReadOutcome) -> PlanReadApply {
        if self.active_plan.is_none() {
            return PlanReadApply::StalePlan;
        }
        let missing = match outcome {
            ReadOutcome::Settled { node: Some(bytes) } => {
                // NodeReadBroker returns the NodeStore payload verbatim. SHAMap
                // NodeStore objects are prefix-form, unlike overlay TMLedgerData
                // nodes (which are decoded by `apply_network_node` as wire form).
                match SHAMapTreeNode::make_from_prefix(bytes, hash) {
                    Ok(mut node) if node.get_hash() == hash => {
                        // Match SHAMap::fetchNodeNT: every verified NodeStore
                        // result is canonicalized through the shared family
                        // before it is attached to this acquisition. Without
                        // this, read-heavy partial trees are owned only by the
                        // current session and cannot seed a replacement plan.
                        self.family.canonicalize(hash, &mut node);
                        MissingNodeReadOutcome::Found(node)
                    }
                    Ok(_) | Err(_) => return PlanReadApply::UnknownRead,
                }
            }
            ReadOutcome::Settled { node: None } => MissingNodeReadOutcome::Miss,
            ReadOutcome::Stale | ReadOutcome::Cancelled => MissingNodeReadOutcome::Cancelled,
        };
        let plan = self
            .active_plan
            .as_mut()
            .expect("active plan checked above");
        Self::map_apply(plan.apply_read_result(self.plan_id, hash, missing))
    }

    fn apply_recovery_read(
        &mut self,
        need: PlanNetworkNeed,
        outcome: &ReadOutcome,
    ) -> PlanReadApply {
        if self.active_kind != Some(need.kind()) {
            return PlanReadApply::StalePlan;
        }
        if self.active_plan.is_none() {
            return PlanReadApply::StalePlan;
        }
        let node = match outcome {
            ReadOutcome::Settled { node: Some(bytes) } => {
                // Recovery data comes from NodeStore in prefix form. It must
                // never be sent through the TMLedgerData wire decoder or the
                // map-level packet path: this exact retained need attaches
                // directly to the active continuation after hash validation.
                let hash = SHAMapHash::new(need.hash());
                match SHAMapTreeNode::make_from_prefix(bytes, hash) {
                    Ok(mut node) if *node.get_hash().as_uint256() == need.hash() => {
                        self.family.canonicalize(hash, &mut node);
                        node
                    }
                    _ => return PlanReadApply::HashMismatch,
                }
            }
            ReadOutcome::Settled { node: None } => return PlanReadApply::UnknownRead,
            ReadOutcome::Stale | ReadOutcome::Cancelled => return PlanReadApply::Cancelled,
        };
        let plan = self
            .active_plan
            .as_mut()
            .expect("active plan checked above");
        Self::map_apply(plan.apply_network_node(self.plan_id, SHAMapHash::new(need.hash()), node))
    }

    fn apply_network_node(
        &mut self,
        kind: TreeKind,
        node: &InboundLedgerNodeData,
    ) -> PlanNetworkApply {
        // Apply the node to its ledger map through the ordinary packet
        // admission path so the SHAMap, the worker store, and the fetch-pack
        // cache observe exactly the same node application as the actor. The
        // node stays cached in the map even when no active plan can attach it.
        let packet = InboundLedgerPacket::new(
            match kind {
                TreeKind::State => InboundLedgerDataType::StateNode,
                TreeKind::Transaction => InboundLedgerDataType::TransactionNode,
            },
            vec![node.clone()],
        );
        let journal = WorkerJournal;
        let config = LedgerConfig::default();
        let stats = match self.inbound.process_packet_with_family_and_config(
            &packet,
            &journal,
            &config,
            &mut self.store,
            &mut self.fetch_pack,
            &self.family,
        ) {
            Ok(stats) => stats,
            Err(_) => return PlanNetworkApply::new(PlanReadApply::UnknownRead, false),
        };
        let useful = stats.is_useful();
        if stats.is_invalid() {
            return PlanNetworkApply::invalid(PlanReadApply::UnknownRead, useful);
        }
        if self.active_kind != Some(kind) {
            // The node belongs to the other tree; the map cached it and it will
            // attach when that tree's plan becomes active.
            return PlanNetworkApply::new(PlanReadApply::StalePlan, useful);
        }
        let Some(plan) = self.active_plan.as_mut() else {
            return PlanNetworkApply::new(PlanReadApply::StalePlan, useful);
        };
        let Ok(Some(decoded)) = SHAMapTreeNode::make_from_wire(&node.node_data) else {
            return PlanNetworkApply::new(PlanReadApply::UnknownRead, useful);
        };
        let Some(node_id) = node.node_id.as_deref().and_then(deserialize_shamap_node_id) else {
            return PlanNetworkApply::invalid(PlanReadApply::UnknownRead, useful);
        };
        let hash = decoded.get_hash();
        // Packet admission already canonicalized every useful backed node.
        // Resume the retained continuation with that exact shared object, not
        // the independent validation decode above. This keeps the map, cache,
        // and continuation in one object graph like rippled's addKnownNode.
        let mut canonical = self.cache.fetch(hash.as_uint256()).unwrap_or(decoded);
        self.family.canonicalize(hash, &mut canonical);
        let applied = Self::map_apply(plan.apply_known_network_node(
            self.plan_id,
            node_id,
            hash,
            canonical.clone(),
        ));
        if matches!(applied, PlanReadApply::Applied { .. }) {
            let _ = self
                .store
                .store_resident_shamap_node(kind, &canonical, self.inbound.seq());
        }
        if matches!(applied, PlanReadApply::HashMismatch) {
            PlanNetworkApply::invalid(applied, useful)
        } else {
            PlanNetworkApply::new(applied, useful)
        }
    }

    fn begin_reply_scan(&mut self) {
        if let Some(plan) = self.active_plan.as_mut() {
            plan.begin_reply_scan();
        }
    }

    fn retain_network_needs(&mut self, needs: &[PlanNetworkNeed]) {
        if let Some(plan) = self.active_plan.as_mut() {
            plan.retain_network_hashes(
                needs
                    .iter()
                    .filter(|need| Some(need.kind()) == self.active_kind)
                    .map(|need| SHAMapHash::new(need.hash())),
            );
        }
    }

    fn rearm_pending_reads(&mut self) {
        if let Some(plan) = self.active_plan.as_mut() {
            plan.rearm_pending_reads();
        }
    }

    fn has_runnable_frontier(&self) -> bool {
        self.active_plan
            .as_ref()
            .is_some_and(TreePlan::has_runnable_frontier)
    }

    fn branch_steps(&self) -> u64 {
        self.cached_root_steps.saturating_add(
            self.active_plan
                .as_ref()
                .map(TreePlan::branch_steps)
                .unwrap_or(0),
        )
    }

    fn ledger_sequence(&self) -> Option<u32> {
        (self.inbound.planner_state().have_header)
            .then(|| self.inbound.seq())
            .filter(|sequence| *sequence != 0)
    }

    fn take_persistable_nodes(&mut self) -> Vec<PersistNode> {
        self.take_accepted_writes()
    }

    fn on_persistence_accepted(&mut self) {
        self.publish_persisted_full_below();
    }

    fn persistence_sequence(&self) -> Option<u32> {
        // InboundLedgerLocal accepts and promotes this sequence only through
        // verified header processing. It is the authority rippled passes to
        // InboundLedgerStore, never a value inferred from a node or key.
        (self.inbound.is_complete())
            .then(|| self.inbound.seq())
            .filter(|sequence| *sequence != 0)
    }

    fn durable_ledger(&mut self) -> Option<Arc<ledger::Ledger>> {
        self.inbound
            .finalize_completed_ledger()
            .then(|| self.inbound.take_ledger().map(Arc::new))
            .flatten()
    }
}

/// One-shot construction of an [`AppLedgerPlanEngine`] from the first
/// Base/header packet of a session.
#[allow(dead_code)] // used by the coordinator adapter in sub-slice M4.2-B
#[derive(Clone)]
pub(crate) struct AppPlanSeed {
    seq: u32,
    reason: InboundLedgerReason,
    fetch_pack: Arc<FetchPackCache>,
    cache: Arc<TreeNodeCache<MonotonicClock>>,
    full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
}

impl std::fmt::Debug for AppPlanSeed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppPlanSeed")
            .field("seq", &self.seq)
            .field("reason", &self.reason)
            .finish()
    }
}

#[allow(dead_code)] // used by the coordinator adapter in sub-slice M4.2-B
impl AppPlanSeed {
    pub(crate) fn new(
        seq: u32,
        reason: InboundLedgerReason,
        fetch_pack: Arc<FetchPackCache>,
        cache: Arc<TreeNodeCache<MonotonicClock>>,
        full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    ) -> Self {
        Self {
            seq,
            reason,
            fetch_pack,
            cache,
            full_below,
        }
    }
}

impl PlanSeed for AppPlanSeed {
    fn build_resident(&mut self, session: SessionRef) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        let blob = self.fetch_pack.get_fetch_pack(session.target_hash())?;
        let header = ledger::deserialize_prefixed_ledger_header(&blob, false).ok()?;
        let packet = InboundLedgerPacket::new(
            InboundLedgerDataType::Base,
            vec![InboundLedgerNodeData::new(
                None,
                protocol::serialize_ledger_header(&header, false),
            )],
        );
        self.build(session, &packet)
    }

    fn build_stored_header(
        &mut self,
        session: SessionRef,
        data: &Bytes,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        let header = ledger::deserialize_prefixed_ledger_header(data, false).ok()?;
        let packet = InboundLedgerPacket::new(
            InboundLedgerDataType::Base,
            vec![InboundLedgerNodeData::new(
                None,
                protocol::serialize_ledger_header(&header, false),
            )],
        );
        self.build(session, &packet)
    }

    fn build(
        &mut self,
        session: SessionRef,
        header: &InboundLedgerPacket,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        build_app_engine(
            session,
            header,
            self.seq,
            self.reason,
            &self.fetch_pack,
            &self.cache,
            &self.full_below,
        )
    }
}

/// Builds a uniquely owned [`AppLedgerPlanEngine`] from the first Base/header
/// packet of a session. Shared by [`AppPlanSeed`] (fixed origin) and
/// [`CoordinatorPlanSeed`] (per-session origin).
fn build_app_engine(
    session: SessionRef,
    header: &InboundLedgerPacket,
    seq: u32,
    reason: InboundLedgerReason,
    fetch_pack: &Arc<FetchPackCache>,
    cache: &Arc<TreeNodeCache<MonotonicClock>>,
    full_below: &Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
) -> Option<Box<dyn TreeEngine + Send + Sync>> {
    let mut inbound =
        InboundLedgerLocal::new_with_reason(SHAMapHash::new(session.target_hash()), seq, reason);
    let mut store = WorkerStore::default();
    let mut worker_fetch_pack = WorkerFetchPack::new(Arc::clone(fetch_pack));
    let family = SHAMapFamily::new(
        Arc::clone(cache),
        Arc::clone(full_below),
        ActorNodeFetcher,
        NullMissingNodeReporter,
    );
    let journal = WorkerJournal;
    let config = LedgerConfig::default();
    let accepted = inbound
        .process_packet_with_family_and_config(
            header,
            &journal,
            &config,
            &mut store,
            &mut worker_fetch_pack,
            &family,
        )
        .is_ok_and(|stats| !stats.is_invalid());
    if !accepted || inbound.is_failed() {
        return None;
    }
    let plan_id = TreePlanId::new(session.session_id().get() + 1);
    Some(Box::new(AppLedgerPlanEngine::new(
        session,
        plan_id,
        inbound,
        store,
        worker_fetch_pack,
        family,
        Arc::clone(cache),
        Arc::clone(full_below),
    )))
}

/// Shared registry of per-session engine origins: target hash → (sequence,
/// reason). The app registers a session's origin exactly once when it requests
/// acquisition; the seed resolves it when the first Base/header packet arrives
/// to build the session engine. The coordinator remains the single lifecycle
/// owner; this map only feeds the one-shot engine constructor.
#[derive(Clone, Default, Debug)]
pub(crate) struct CoordinatorSessionOrigins {
    map: Arc<RwLock<BTreeMap<Uint256, (u32, InboundLedgerReason)>>>,
}

impl CoordinatorSessionOrigins {
    /// Registers the origin of one requested session. A deferred consensus
    /// demand remains authoritative for the same target until it binds a
    /// session; Generic/History polling must not replace its sequence or
    /// reason before the later Base packet builds the engine.
    pub(crate) fn register(&self, target: Uint256, seq: u32, reason: InboundLedgerReason) {
        let mut origins = self.map.write().expect("session origin lock");
        if origins.get(&target).is_some_and(|(_, current)| {
            *current == InboundLedgerReason::Consensus && reason != InboundLedgerReason::Consensus
        }) {
            return;
        }
        origins.insert(target, (seq, reason));
    }

    fn resolve(&self, target: Uint256) -> Option<(u32, InboundLedgerReason)> {
        self.map
            .read()
            .expect("session origin lock")
            .get(&target)
            .copied()
    }

    pub(crate) fn remove(&self, target: Uint256) {
        self.map
            .write()
            .expect("session origin lock")
            .remove(&target);
    }

    /// Drop provenance whose coordinator demand was superseded before it
    /// minted a session. The runner bounds peerless ordinary work to its
    /// newest target, so this sidecar map must follow the same ownership set.
    pub(crate) fn retain_targets(&self, mut retain: impl FnMut(Uint256) -> bool) {
        self.map
            .write()
            .expect("session origin lock")
            .retain(|target, _| retain(*target));
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.map.read().expect("session origin lock").len()
    }
}

/// Production [`PlanSeed`] for the coordinator adapter: resolves each session's
/// `(sequence, reason)` origin through a shared [`CoordinatorSessionOrigins`]
/// and builds an [`AppLedgerPlanEngine`] over the shared tree caches.
pub(crate) struct CoordinatorPlanSeed {
    origins: CoordinatorSessionOrigins,
    fetch_pack: Arc<FetchPackCache>,
    cache: Arc<TreeNodeCache<MonotonicClock>>,
    full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
}

impl std::fmt::Debug for CoordinatorPlanSeed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoordinatorPlanSeed")
            .field("origins", &self.origins)
            .finish()
    }
}

impl CoordinatorPlanSeed {
    pub(crate) fn new(
        origins: CoordinatorSessionOrigins,
        fetch_pack: Arc<FetchPackCache>,
        cache: Arc<TreeNodeCache<MonotonicClock>>,
        full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    ) -> Self {
        Self {
            origins,
            fetch_pack,
            cache,
            full_below,
        }
    }
}

impl PlanSeed for CoordinatorPlanSeed {
    fn session_reaped(&mut self, session: SessionRef) {
        self.origins.remove(session.target_hash());
    }

    fn build_resident(&mut self, session: SessionRef) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        let blob = self.fetch_pack.get_fetch_pack(session.target_hash())?;
        let header = ledger::deserialize_prefixed_ledger_header(&blob, false).ok()?;
        let packet = InboundLedgerPacket::new(
            InboundLedgerDataType::Base,
            vec![InboundLedgerNodeData::new(
                None,
                protocol::serialize_ledger_header(&header, false),
            )],
        );
        self.build(session, &packet)
    }

    fn build_stored_header(
        &mut self,
        session: SessionRef,
        data: &Bytes,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        let header = ledger::deserialize_prefixed_ledger_header(data, false).ok()?;
        let packet = InboundLedgerPacket::new(
            InboundLedgerDataType::Base,
            vec![InboundLedgerNodeData::new(
                None,
                protocol::serialize_ledger_header(&header, false),
            )],
        );
        self.build(session, &packet)
    }

    fn build(
        &mut self,
        session: SessionRef,
        header: &InboundLedgerPacket,
    ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
        let (seq, reason) = self.origins.resolve(session.target_hash())?;
        build_app_engine(
            session,
            header,
            seq,
            reason,
            &self.fetch_pack,
            &self.cache,
            &self.full_below,
        )
    }
}

#[cfg(test)]
mod tests {
    use basics::base_uint::Uint256;
    use basics::hardened_hash::HardenedHashBuilder;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::MonotonicClock;
    use bytes::Bytes;
    use ledger::{
        FetchPackCache, LedgerHeader, TreeKind, calculate_ledger_hash, serialize_ledger_header,
    };
    use shamap::node_id::SHAMapNodeId;
    use shamap::nodes::item::SHAMapItem;
    use shamap::nodes::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use shamap::tree_node_cache::TreeNodeCache;
    use time::Duration;

    use acquisition::{
        PlanEpoch, PlanReadApply, ReadOutcome, RunEpoch, SessionId, SessionRef, StoreGeneration,
    };

    use super::*;

    const SEQ: u32 = 77;

    fn session_for(header: &LedgerHeader) -> SessionRef {
        SessionRef::new(
            RunEpoch::new(1),
            SessionId::new(42),
            *calculate_ledger_hash(header).as_uint256(),
            PlanEpoch::new(1),
            StoreGeneration::new(1),
        )
    }

    fn seed_parts(
        seq: u32,
    ) -> (
        AppPlanSeed,
        Arc<TreeNodeCache<MonotonicClock>>,
        Arc<FetchPackCache>,
    ) {
        let cache = Arc::new(TreeNodeCache::new(
            "coordinator-engine-tests",
            256,
            Duration::seconds(60),
            MonotonicClock::default(),
        ));
        let full_below = Arc::new(FullBelowCacheImpl::new(
            1,
            MonotonicClock::default(),
            HardenedHashBuilder::default(),
            256,
        ));
        let fetch_pack = Arc::new(FetchPackCache::new(
            8,
            Duration::seconds(60),
            MonotonicClock::default(),
        ));
        (
            AppPlanSeed::new(
                seq,
                InboundLedgerReason::Generic,
                Arc::clone(&fetch_pack),
                Arc::clone(&cache),
                Arc::clone(&full_below),
            ),
            cache,
            fetch_pack,
        )
    }

    fn seed_with(seq: u32) -> (AppPlanSeed, Arc<TreeNodeCache<MonotonicClock>>) {
        let (seed, cache, _) = seed_parts(seq);
        (seed, cache)
    }

    /// A one-leaf state tree: root inner with a single AccountState leaf at
    /// branch 5. The leaf is resident in the shared cache so the plan can
    /// attach it without a read or a network round trip.
    fn state_tree(
        cache: &TreeNodeCache<MonotonicClock>,
        fill: u8,
    ) -> (SharedIntrusive<SHAMapTreeNode>, SHAMapHash) {
        let mut leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([fill; 32]), vec![0u8; 32]),
            0,
        );
        let leaf_hash = leaf.get_hash();
        cache.canonicalize_replace_client(leaf_hash.as_uint256(), &mut leaf);
        let root = SHAMapTreeNode::new_inner(0);
        root.set_child_hash(5, leaf_hash);
        root.update_hash();
        (root, leaf_hash)
    }

    fn tx_tree(
        cache: &TreeNodeCache<MonotonicClock>,
        fill: u8,
    ) -> (SharedIntrusive<SHAMapTreeNode>, SHAMapHash) {
        let mut leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(Uint256::from_array([fill; 32]), vec![0u8; 32]),
            0,
        );
        let leaf_hash = leaf.get_hash();
        cache.canonicalize_replace_client(leaf_hash.as_uint256(), &mut leaf);
        let root = SHAMapTreeNode::new_inner(0);
        root.set_child_hash(4, leaf_hash);
        root.update_hash();
        (root, leaf_hash)
    }

    fn base_packet(header: &LedgerHeader) -> InboundLedgerPacket {
        InboundLedgerPacket::new(
            InboundLedgerDataType::Base,
            vec![InboundLedgerNodeData::new(
                None,
                serialize_ledger_header(header, false),
            )],
        )
    }

    fn base_packet_with_state_root(
        header: &LedgerHeader,
        root: &SharedIntrusive<SHAMapTreeNode>,
    ) -> InboundLedgerPacket {
        InboundLedgerPacket::new(
            InboundLedgerDataType::Base,
            vec![
                InboundLedgerNodeData::new(None, serialize_ledger_header(header, false)),
                InboundLedgerNodeData::new(
                    None,
                    root.serialize_for_wire().expect("root serializes as wire"),
                ),
            ],
        )
    }

    fn root_node_data(node: &SharedIntrusive<SHAMapTreeNode>) -> InboundLedgerNodeData {
        InboundLedgerNodeData::new(
            Some(SHAMapNodeId::default().get_raw_string()),
            node.serialize_for_wire().expect("node serializes"),
        )
    }

    fn expect_root_request(engine: &mut dyn TreeEngine, root_hash: SHAMapHash) {
        match engine.advance(10) {
            PlanStepOutcome::NeedsNetwork(nodes) => {
                assert_eq!(nodes.len(), 1, "one root node announced");
                let need = nodes[0];
                assert!(need.node_id().is_root(), "root node id");
                assert_eq!(*root_hash.as_uint256(), need.hash(), "root hash");
                assert_eq!(need.kind(), TreeKind::State, "root tree kind");
            }
            other => panic!("expected root-node request, got {other:?}"),
        }
    }

    #[test]
    fn valid_header_builds_engine_and_requests_root_node() {
        let (mut seed, cache) = seed_with(SEQ);
        let (root, _leaf) = state_tree(&cache, 7);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");
        expect_root_request(engine.as_mut(), root.get_hash());
    }

    #[test]
    fn bundled_base_root_in_canonical_wire_reaches_a_complete_tree_plan() {
        let (mut seed, cache) = seed_with(SEQ);
        let (root, _leaf) = state_tree(&cache, 0xA1);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(
                session_for(&header),
                &base_packet_with_state_root(&header, &root),
            )
            .expect("canonical Base root must build the coordinator engine");

        assert!(matches!(engine.advance(10), PlanStepOutcome::Complete));
    }

    #[test]
    fn seed_rejects_invalid_header_and_seq_mismatch() {
        let (mut seed, _cache) = seed_with(SEQ);
        let bad = InboundLedgerPacket::new(
            InboundLedgerDataType::Base,
            vec![InboundLedgerNodeData::new(None, vec![1, 2, 3])],
        );
        assert!(
            seed.build(session_for(&LedgerHeader::default()), &bad)
                .is_none()
        );

        let mut seed = seed_with(SEQ).0;
        let header = LedgerHeader {
            seq: SEQ + 1,
            ..LedgerHeader::default()
        };
        assert!(
            seed.build(session_for(&header), &base_packet(&header))
                .is_none(),
            "seed seq must match the header seq"
        );
    }

    #[test]
    fn engine_completes_fully_resident_state_tree() {
        let (mut seed, cache) = seed_with(SEQ);
        let (root, _leaf) = state_tree(&cache, 7);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");
        expect_root_request(engine.as_mut(), root.get_hash());

        let applied = engine.apply_network_node(TreeKind::State, &root_node_data(&root));
        assert_eq!(
            applied.attachment(),
            PlanReadApply::StalePlan,
            "no plan is active yet"
        );

        match engine.advance(10) {
            PlanStepOutcome::Complete => {}
            other => panic!("expected complete after rooted state plan, got {other:?}"),
        }

        let persistable = engine.take_persistable_nodes();
        assert!(
            !persistable.is_empty(),
            "header and accepted nodes persist together"
        );
        assert!(
            engine.take_persistable_nodes().is_empty(),
            "accepted writes drain incrementally and are never replayed"
        );
    }

    #[test]
    fn coordinator_durable_ledger_finalizes_zero_tx_root_before_handoff() {
        let (mut seed, cache) = seed_with(SEQ);
        let (root, _leaf) = state_tree(&cache, 7);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");
        expect_root_request(engine.as_mut(), root.get_hash());

        assert_eq!(
            engine
                .apply_network_node(TreeKind::State, &root_node_data(&root))
                .attachment(),
            PlanReadApply::StalePlan,
            "root is installed before the retained traversal starts"
        );
        assert!(matches!(engine.advance(10), PlanStepOutcome::Complete));

        let ledger = engine
            .durable_ledger()
            .expect("complete zero-tx ledger materializes for durable handoff");
        assert!(ledger.is_immutable());
        assert!(!ledger.state_map().is_synching());
        assert!(!ledger.tx_map().is_synching());
        assert!(
            engine.durable_ledger().is_none(),
            "durable handoff takes ledger ownership exactly once"
        );
    }

    #[test]
    fn read_resolves_missing_state_child_and_canonicalizes_it_for_reuse() {
        let (mut seed, cache) = seed_with(SEQ);
        let root = SHAMapTreeNode::new_inner(0);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([8u8; 32]), vec![0u8; 32]),
            0,
        );
        let leaf_hash = leaf.get_hash();
        root.set_child_hash(5, leaf_hash);
        root.update_hash();
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");
        expect_root_request(engine.as_mut(), root.get_hash());
        engine.apply_network_node(TreeKind::State, &root_node_data(&root));

        let PlanStepOutcome::NeedsReads(reads) = engine.advance(10) else {
            panic!("expected a read need for the missing leaf")
        };
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].hash(), leaf_hash);
        assert_eq!(reads[0].branch(), 5);

        let applied = engine.apply_read(
            leaf_hash,
            &ReadOutcome::Settled {
                node: Some(Bytes::from(
                    leaf.serialize_with_prefix()
                        .expect("leaf serializes for NodeStore"),
                )),
            },
        );
        assert!(
            matches!(
                applied,
                PlanReadApply::Applied {
                    attached_edges: 1,
                    ..
                }
            ),
            "leaf attaches to the root edge"
        );
        let cached = cache
            .fetch(leaf_hash.as_uint256())
            .expect("a verified NodeStore result must enter the shared tree cache");
        assert_eq!(cached.get_hash(), leaf_hash);

        match engine.advance(10) {
            PlanStepOutcome::Complete => {}
            other => panic!("expected complete after read, got {other:?}"),
        }
    }

    #[test]
    fn durable_read_full_below_survives_engine_replacement_and_cache_sweep() {
        let (mut seed, cache) = seed_with(SEQ);
        let full_below = Arc::clone(&seed.full_below);
        let root = SHAMapTreeNode::new_inner(0);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0xD4; 32]), vec![0u8; 32]),
            0,
        );
        let leaf_hash = leaf.get_hash();
        root.set_child_hash(5, leaf_hash);
        root.update_hash();
        let root_hash = root.get_hash();
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root_hash,
            ..LedgerHeader::default()
        };
        let session = session_for(&header);
        let mut first = seed
            .build(session, &base_packet(&header))
            .expect("first engine");
        expect_root_request(first.as_mut(), root_hash);
        first.apply_network_node(TreeKind::State, &root_node_data(&root));

        let PlanStepOutcome::NeedsReads(reads) = first.advance(10) else {
            panic!("first engine must request its missing durable leaf")
        };
        // The Base and network root are not durable until this accepted batch.
        assert!(!first.take_persistable_nodes().is_empty());
        first.on_persistence_accepted();
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].hash(), leaf_hash);
        assert!(matches!(
            first.apply_read(
                leaf_hash,
                &ReadOutcome::Settled {
                    node: Some(Bytes::from(
                        leaf.serialize_with_prefix().expect("leaf serializes")
                    )),
                }
            ),
            PlanReadApply::Applied { .. }
        ));
        assert!(matches!(first.advance(10), PlanStepOutcome::Complete));
        assert!(
            first.take_persistable_nodes().is_empty(),
            "a verified NodeStore read requires no replacement write"
        );
        assert!(
            full_below.touch_if_exists(*root_hash.as_uint256()),
            "an all-durable subtree publishes FullBelow without waiting for a nonexistent write"
        );

        // Dropping the cancelled/replaced engine releases its private plan,
        // then an ordinary shared-cache sweep runs between sessions.
        drop(first);
        cache.sweep();

        let mut replacement = seed
            .build(session, &base_packet(&header))
            .expect("replacement engine");
        assert!(
            matches!(replacement.advance(10), PlanStepOutcome::Complete),
            "replacement reuses the cached root plus process-wide FullBelow marker"
        );
    }

    #[test]
    fn fetch_pack_installs_missing_state_root_without_a_ledger_data_packet() {
        // Generic TMGetObjectByHash replies populate fetch-pack, not the
        // TMLedgerData router. The engine must consume a cached root before it
        // has an active tree plan, otherwise every wake only repeats the root
        // request indefinitely.
        let (mut seed, _cache, fetch_pack) = seed_parts(SEQ);
        let root = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0x2B; 32]), vec![0u8; 32]),
            0,
        );
        fetch_pack.add_fetch_pack(
            *root.get_hash().as_uint256(),
            root.serialize_with_prefix().expect("root serializes"),
        );
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");
        assert_eq!(
            engine.ledger_sequence(),
            Some(SEQ),
            "a hash-only session must promote its verified Base sequence before node requests"
        );

        // No direct root packet is applied. The cached by-hash root is
        // installed, its state tree starts, and the complete ledger emerges.
        let before = engine.branch_steps();
        match engine.advance(10) {
            PlanStepOutcome::Complete => {}
            other => panic!("expected complete via cached root, got {other:?}"),
        }
        assert!(
            engine.branch_steps() > before,
            "successful cached-root application must count as session-local progress"
        );
    }

    #[test]
    fn fetch_pack_resolves_missing_state_child_without_a_read() {
        // The leaf is present only in the fetch-pack cache, not in the shared
        // tree cache, so its resolution proves the by-hash resident lookup.
        let (mut seed, _cache, fetch_pack) = seed_parts(SEQ);
        let root = SHAMapTreeNode::new_inner(0);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0x1A; 32]), vec![0u8; 32]),
            0,
        );
        let leaf_hash = leaf.get_hash();
        fetch_pack.add_fetch_pack(
            *leaf_hash.as_uint256(),
            leaf.serialize_with_prefix().expect("leaf serializes"),
        );
        root.set_child_hash(5, leaf_hash);
        root.update_hash();
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");
        expect_root_request(engine.as_mut(), root.get_hash());
        engine.apply_network_node(TreeKind::State, &root_node_data(&root));

        // The traversal resolves the fetch-pack leaf as resident: no read need
        // is announced and the state plan completes.
        match engine.advance(10) {
            PlanStepOutcome::Complete => {}
            other => panic!("expected complete via fetch-pack, got {other:?}"),
        }

        // Control: without the fetch-pack entry, the same tree needs a read.
        let (mut seed, _cache, _fetch_pack) = seed_parts(SEQ);
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header rebuilds an engine");
        expect_root_request(engine.as_mut(), root.get_hash());
        engine.apply_network_node(TreeKind::State, &root_node_data(&root));
        let PlanStepOutcome::NeedsReads(reads) = engine.advance(10) else {
            panic!("without the fetch-pack the missing leaf needs a read")
        };
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].hash(), leaf_hash);
    }

    #[test]
    fn wrong_kind_network_node_is_cached_for_later_plan() {
        let (mut seed, cache) = seed_with(SEQ);
        let (state_root, _) = state_tree(&cache, 7);
        let (tx_root, _) = tx_tree(&cache, 9);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: state_root.get_hash(),
            tx_hash: tx_root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");
        expect_root_request(engine.as_mut(), state_root.get_hash());

        // A transaction root arrives before its tree's plan exists; the map
        // caches it and the engine reports the attach as stale.
        let applied = engine.apply_network_node(TreeKind::Transaction, &root_node_data(&tx_root));
        assert_eq!(applied.attachment(), PlanReadApply::StalePlan);

        engine.apply_network_node(TreeKind::State, &root_node_data(&state_root));

        // The single advance runs the state plan, then the transaction plan
        // over the already-cached transaction root, and reports completion.
        match engine.advance(10) {
            PlanStepOutcome::Complete => {}
            other => panic!("expected complete for both trees, got {other:?}"),
        }
    }

    #[test]
    fn stale_and_malformed_store_reads_are_rejected() {
        let (mut seed, _cache) = seed_with(SEQ);
        // A root whose only child is absent from the cache, so the plan must
        // request a read before it can complete.
        let root = SHAMapTreeNode::new_inner(0);
        let missing = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0x77; 32]), vec![0u8; 32]),
            0,
        );
        let missing_hash = missing.get_hash();
        root.set_child_hash(5, missing_hash);
        root.update_hash();
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let mut engine = seed
            .build(session_for(&header), &base_packet(&header))
            .expect("valid header builds an engine");

        assert_eq!(
            engine.apply_read(SHAMapHash::default(), &ReadOutcome::Stale),
            PlanReadApply::StalePlan,
            "a read with no active plan is stale"
        );

        expect_root_request(engine.as_mut(), root.get_hash());
        engine.apply_network_node(TreeKind::State, &root_node_data(&root));

        let PlanStepOutcome::NeedsReads(reads) = engine.advance(10) else {
            panic!("expected a read need for the missing leaf")
        };
        let other = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0xAA; 32]), vec![0u8; 32]),
            0,
        );
        let applied = engine.apply_read(
            reads[0].hash(),
            &ReadOutcome::Settled {
                node: Some(Bytes::from(
                    other
                        .serialize_for_wire()
                        .expect("node serializes for the wire"),
                )),
            },
        );
        assert_eq!(applied, PlanReadApply::UnknownRead);
    }

    fn coordinator_resources() -> (
        CoordinatorPlanSeed,
        CoordinatorSessionOrigins,
        Arc<TreeNodeCache<MonotonicClock>>,
    ) {
        let cache = Arc::new(TreeNodeCache::new(
            "coordinator-seed-tests",
            256,
            Duration::seconds(60),
            MonotonicClock::default(),
        ));
        let full_below = Arc::new(FullBelowCacheImpl::new(
            1,
            MonotonicClock::default(),
            HardenedHashBuilder::default(),
            256,
        ));
        let fetch_pack = Arc::new(FetchPackCache::new(
            8,
            Duration::seconds(60),
            MonotonicClock::default(),
        ));
        let origins = CoordinatorSessionOrigins::default();
        let seed = CoordinatorPlanSeed::new(
            origins.clone(),
            Arc::clone(&fetch_pack),
            Arc::clone(&cache),
            Arc::clone(&full_below),
        );
        (seed, origins, cache)
    }

    #[test]
    fn full_below_mark_stays_session_private_until_persistence_accepts() {
        let cache = TreeNodeCache::new(
            "full-below-staging-test",
            8,
            Duration::seconds(60),
            MonotonicClock::default(),
        );
        let shared = FullBelowCacheImpl::new(
            1,
            MonotonicClock::default(),
            HardenedHashBuilder::default(),
            8,
        );
        let node = SHAMapTreeNode::new_inner(0);
        node.set_child_hash(0, SHAMapHash::new(Uint256::from(0xAB)));
        node.update_hash();
        let hash = node.get_hash();
        let fetch_pack = FetchPackCache::new(8, Duration::seconds(60), MonotonicClock::default());
        let mut staged = BTreeMap::new();
        let mut store = WorkerStore::default();
        assert!(store.store_resident_shamap_node(TreeKind::State, &node, SEQ));
        {
            let mut resident = AppResident {
                cache: &cache,
                shared_full_below: &shared,
                pending_full_below: &mut staged,
                fetch_pack: &fetch_pack,
                store: &mut store,
                kind: TreeKind::State,
            };
            resident.mark_full_below(node.clone(), 1);
            assert!(!node.is_full_below(1));
            assert!(
                !resident.is_full_below(hash),
                "an unpersisted marker must not be visible to another traversal"
            );
        }
        assert!(staged.contains_key(hash.as_uint256()));
        assert!(
            !shared.touch_if_exists(*hash.as_uint256()),
            "the shared cache stays empty before write acceptance"
        );
        for (marker, (node, generation)) in staged {
            node.set_full_below_gen(generation);
            shared.insert(marker);
        }
        assert!(
            shared.touch_if_exists(*hash.as_uint256()),
            "publication after write acceptance makes the marker shared"
        );
    }

    #[test]
    fn shared_cache_resident_waits_for_persistence_before_full_below_publication() {
        let cache = TreeNodeCache::new(
            "cache-resident-durability-test",
            8,
            Duration::seconds(60),
            MonotonicClock::default(),
        );
        let shared = FullBelowCacheImpl::new(
            1,
            MonotonicClock::default(),
            HardenedHashBuilder::default(),
            8,
        );
        let fetch_pack = FetchPackCache::new(8, Duration::seconds(60), MonotonicClock::default());
        let mut node = SHAMapTreeNode::new_inner(0);
        node.set_child_hash(0, SHAMapHash::new(Uint256::from(0xD1)));
        node.update_hash();
        let hash = node.get_hash();
        cache.canonicalize_replace_client(hash.as_uint256(), &mut node);

        let mut staged = BTreeMap::new();
        let mut store = WorkerStore::default();
        {
            let mut resident = AppResident {
                cache: &cache,
                shared_full_below: &shared,
                pending_full_below: &mut staged,
                fetch_pack: &fetch_pack,
                store: &mut store,
                kind: TreeKind::State,
            };
            let loaded = resident
                .load_resident(hash, SEQ)
                .expect("shared cache node resolves");
            resident.mark_full_below(loaded, 1);
            assert!(
                !resident.is_full_below(hash),
                "cache-only provenance must not become cross-session state"
            );
        }

        assert_eq!(store.take_pending_write_nodes().len(), 1);
        assert!(staged.contains_key(hash.as_uint256()));
        assert!(!shared.touch_if_exists(*hash.as_uint256()));
        for (marker, (node, generation)) in staged {
            node.set_full_below_gen(generation);
            shared.insert(marker);
        }
        assert!(shared.touch_if_exists(*hash.as_uint256()));
    }

    #[test]
    fn fetch_pack_resident_is_canonicalized_and_queued_for_persistence() {
        let cache = TreeNodeCache::new(
            "fetch-pack-resident-test",
            8,
            Duration::seconds(60),
            MonotonicClock::default(),
        );
        let shared = FullBelowCacheImpl::new(
            1,
            MonotonicClock::default(),
            HardenedHashBuilder::default(),
            8,
        );
        let fetch_pack = FetchPackCache::new(8, Duration::seconds(60), MonotonicClock::default());
        let node = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0xBC; 32]), vec![0xBC; 32]),
            0,
        );
        let hash = node.get_hash();
        fetch_pack.add_fetch_pack(
            *hash.as_uint256(),
            node.serialize_with_prefix().expect("node serializes"),
        );
        let mut staged = BTreeMap::new();
        let mut store = WorkerStore::default();

        let loaded = {
            let mut resident = AppResident {
                cache: &cache,
                shared_full_below: &shared,
                pending_full_below: &mut staged,
                fetch_pack: &fetch_pack,
                store: &mut store,
                kind: TreeKind::State,
            };
            resident
                .load_resident(hash, SEQ)
                .expect("fetch-pack node resolves")
        };

        let cached = cache
            .fetch(hash.as_uint256())
            .expect("node is canonicalized");
        assert_eq!(cached.get_hash(), loaded.get_hash());
        let writes = store.take_pending_write_nodes();
        assert_eq!(writes.len(), 1);
        assert_eq!(writes[0].key(), hash);
        assert_eq!(
            writes[0].object_kind(),
            acquisition::StoredObjectKind::AccountNode
        );
        drop(cached);
        drop(loaded);
    }

    #[test]
    fn coordinator_seed_resolves_per_session_origin() {
        let (mut seed, origins, cache) = coordinator_resources();
        let (root, _leaf) = state_tree(&cache, 7);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let session = session_for(&header);

        assert!(
            seed.build(session, &base_packet(&header)).is_none(),
            "an unregistered target builds no engine"
        );

        origins.register(session.target_hash(), SEQ, InboundLedgerReason::Generic);
        let mut engine = seed
            .build(session, &base_packet(&header))
            .expect("a registered origin builds an engine");
        expect_root_request(engine.as_mut(), root.get_hash());
    }

    #[test]
    fn coordinator_seed_replaces_an_origin_for_later_builds() {
        let (mut seed, origins, cache) = coordinator_resources();
        let (root, _leaf) = state_tree(&cache, 7);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let session = session_for(&header);

        origins.register(session.target_hash(), SEQ, InboundLedgerReason::Generic);
        assert!(
            seed.build(session, &base_packet(&header)).is_some(),
            "matching origin builds an engine"
        );

        // Re-registering with a sequence that contradicts the header proves the
        // replacement origin is what the next build resolves.
        origins.register(
            session.target_hash(),
            SEQ + 1,
            InboundLedgerReason::Consensus,
        );
        assert!(
            seed.build(session, &base_packet(&header)).is_none(),
            "a replaced origin drives later builds"
        );
    }

    #[test]
    fn coordinator_seed_preserves_consensus_origin_against_same_hash_lower_priority_calls() {
        let (mut seed, origins, cache) = coordinator_resources();
        let (root, _leaf) = state_tree(&cache, 7);
        let header = LedgerHeader {
            seq: SEQ,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        let session = session_for(&header);

        origins.register(session.target_hash(), SEQ, InboundLedgerReason::Consensus);
        origins.register(session.target_hash(), SEQ + 1, InboundLedgerReason::Generic);
        let mut engine = seed
            .build(session, &base_packet(&header))
            .expect("the original consensus sequence still builds the engine");
        expect_root_request(engine.as_mut(), root.get_hash());
    }

    #[test]
    fn coordinator_seed_keeps_distinct_targets_isolated() {
        let (mut seed, origins, cache) = coordinator_resources();
        let (state_root, _) = state_tree(&cache, 7);
        let (tx_root, _) = tx_tree(&cache, 9);
        let first = LedgerHeader {
            seq: SEQ,
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        };
        let second = LedgerHeader {
            seq: SEQ + 1,
            account_hash: tx_root.get_hash(),
            tx_hash: tx_root.get_hash(),
            ..LedgerHeader::default()
        };
        let first_session = session_for(&first);
        let second_session = session_for(&second);

        origins.register(
            first_session.target_hash(),
            SEQ,
            InboundLedgerReason::Generic,
        );
        assert!(
            seed.build(first_session, &base_packet(&first)).is_some(),
            "the registered target builds"
        );
        assert!(
            seed.build(second_session, &base_packet(&second)).is_none(),
            "an unregistered distinct target still builds nothing"
        );
    }

    #[test]
    fn withdrawn_validation_candidates_do_not_grow_session_origins() {
        let origins = CoordinatorSessionOrigins::default();
        let anchor = Uint256::from(1);
        origins.register(anchor, 1, InboundLedgerReason::Consensus);
        for sequence in 2..=128 {
            let candidate = Uint256::from(sequence);
            origins.register(candidate, sequence as u32, InboundLedgerReason::Consensus);
            origins.remove(candidate);
        }
        assert_eq!(origins.len(), 1);
        assert_eq!(
            origins.resolve(anchor),
            Some((1, InboundLedgerReason::Consensus))
        );
    }
}
