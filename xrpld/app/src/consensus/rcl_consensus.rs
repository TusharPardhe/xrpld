//! App-level wiring of the generic `Consensus<Adaptor>` state machine
//! against real `Ledger`/`SHAMap`/`STValidation`/`ValidatorList` types.
//! Ported from `RCLConsensus.h`/`RCLConsensus.cpp`.
//!
//! This module defines:
//! - [`RclConsensusOpenLedgerSource`]: the open-ledger view the adaptor
//!   reads current transactions from and resets on ledger acceptance.
//! - [`RclConsensusValidationSource`]: the validation-tracking surface the
//!   adaptor needs (trusted proposer counts, preferred ledger).
//! - [`AppRclConsensusOptions`]: standalone/timing overrides.
//! - [`AppRclConsensusRelay`]: peer broadcast of proposals/tx-sets/etc.
//! - [`NullRclConsensusJournal`]: a no-op diagnostics sink.
//! - [`AppRclConsensusAdaptor`]: the `ConsensusAdaptor` implementation.
//! - [`ConsensusRunner`] / [`AppConsensus`]: the single-strand consensus
//!   driver that owns `Consensus<AppRclConsensusAdaptor>` directly on the
//!   strand thread with NO mutex (matching rippled's single-strand model).
//!
//! ## Single-Strand Model
//!
//! In rippled, consensus runs on a single strand: "In general, the idea is
//! that there is only ONE thread that is running consensus code at anytime."
//! (RCLConsensus.h:168-170). This port matches that exactly:
//! - `AppConsensus` is owned by value on the strand thread
//! - All methods take `&mut self` (no interior mutability needed)
//! - No mutex protects the `Consensus` state machine
//! - Proposals, timer_entry, and accept all run on the same thread in FIFO order
//!
//! ## Two ledger types: `RclCxLedger` vs `RclValidatedLedger`
//!
//! The `Consensus<Adaptor>::Ledger` associated type must implement
//! `consensus::ConsensusLedger` (id/seq/close-time accessors only) —
//! that's [`consensus::RclCxLedger`], a thin wrapper over `Arc<Ledger>`.
//! The validation tracker instead needs `ValidationsLedger`
//! (ancestor-trie lookups for Byzantine-safe preference resolution) —
//! that's [`crate::consensus::rcl_validation::RclValidatedLedger`], a
//! *different* concrete type with its own eagerly-cached ancestor vector.

use basics::unordered_containers::HashSet;
use std::collections::HashSet as StdHashSet;
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::{Arc, Mutex as StdMutex};
use std::time::Duration as StdDuration;

use basics::base_uint::Uint256;
use basics::chrono::NetClockTimePoint;
use basics::sha_map_hash::SHAMapHash;
use consensus::algorithm::types::{ConsensusCloseTimes, ConsensusMode};
use consensus::model::TrieLedger;
use consensus::rcl_support::ValidationsLedger;
use consensus::{Consensus, ConsensusParms};
use protocol::PublicKey;

use crate::consensus::censorship_detector::{CensorshipDetector, TxIDSeq};
use crate::consensus::rcl_cx_peer_pos::{Proposal, RclCxPeerPos, sign_proposal};
use crate::consensus::rcl_validations::SharedAppValidations;
use crate::job::job_types::JobType;
use crate::ledger::ledger_master_runtime::AppLedgerMasterRuntime;
use crate::load::fee_vote::FeeVote;
use crate::network::network_ops::{AppNetworkOpsModeOwner, NetworkOpsOperatingMode};
use crate::state::app_registry::{AppInboundTransactions, SharedAppOpenLedger};
use crate::state::application_root::{ApplicationRoot, LedgerAcceptor};
use crate::state::time_keeper::{SystemTimeKeeperClock, TimeKeeper};
use crate::tx_queue::transaction::Transaction;
use crate::tx_queue::transaction_master::TransactionMaster;
use crate::validator::validator_keys::ValidatorKeys;
use crate::validator::validator_list::ValidatorList;
use ledger::CanonicalTXSet;

pub type RclCxTx = consensus::RclCxTx;
pub type RclCxLedger = consensus::RclCxLedger;

fn panic_payload_message(payload: Box<dyn std::any::Any + Send>) -> String {
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| {
            payload
                .downcast_ref::<&str>()
                .map(|message| (*message).to_owned())
        })
        .unwrap_or_else(|| "non-string panic payload".to_owned())
}

/// Decode peer-supplied consensus transaction bytes at the same boundary where
/// rippled constructs its canonical consensus transaction set. A malformed
/// entry is reported but does not prevent valid entries from being applied.
fn decode_consensus_accept_transactions<'a>(
    tx_set_id: Uint256,
    items: impl IntoIterator<Item = (usize, &'a [u8])>,
) -> (Vec<Arc<protocol::STTx>>, Vec<(usize, String)>) {
    let mut txns = CanonicalTXSet::new(tx_set_id);
    let mut malformed = Vec::new();

    for (payload_len, bytes) in items {
        if !(protocol::TX_MIN_SIZE_BYTES..=protocol::TX_MAX_SIZE_BYTES).contains(&payload_len) {
            malformed.push((
                payload_len,
                format!("transaction payload length {payload_len} is outside the legal range"),
            ));
            continue;
        }

        let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut sit: protocol::SerialIter<'_> = bytes.into();
            let tx = protocol::STTx::from_serial_iter(&mut sit);
            if !sit.empty() {
                return Err("transaction payload has trailing bytes".to_owned());
            }
            Ok(tx)
        }));
        match parsed {
            Ok(Ok(tx)) => txns.insert(Arc::new(tx)),
            Ok(Err(message)) => malformed.push((payload_len, message)),
            Err(payload) => malformed.push((payload_len, panic_payload_message(payload))),
        }
    }

    (txns.drain_ordered(), malformed)
}

fn canonicalize_consensus_transaction(
    transaction_master: &TransactionMaster,
    transaction: Arc<protocol::STTx>,
) -> Arc<protocol::STTx> {
    let mut canonical = Arc::new(StdMutex::new(Transaction::new(transaction)));
    transaction_master.canonicalize(&mut canonical);
    Arc::clone(
        canonical
            .lock()
            .expect("canonical consensus transaction mutex must not be poisoned")
            .get_s_transaction(),
    )
}

/// Return rippled's `medianCloseOffset`: the lower weighted median of our
/// close time (weight one) and peer close-time vote bins, minus our own close
/// time. A rounded mean changes the next proposal time in a two-validator
/// split and does not match rippled.
fn median_close_offset_seconds(times: &ConsensusCloseTimes) -> i64 {
    let total_weight = 1_i64
        + times
            .peers
            .values()
            .map(|weight| i64::from(*weight))
            .sum::<i64>();
    let half_weight = (total_weight + 1) / 2;
    let self_time = times.self_;
    let mut tally = 0_i64;
    let mut self_placed = false;

    for (time, weight) in &times.peers {
        if !self_placed && self_time <= *time {
            self_placed = true;
            tally += 1;
            if tally >= half_weight {
                return 0;
            }
        }
        tally += i64::from(*weight);
        if tally >= half_weight {
            return i64::from(time.as_seconds()) - i64::from(self_time.as_seconds());
        }
    }

    // The self sample is the final ordered bin, so it is the lower median if
    // no preceding peer bin reached the threshold.
    0
}

fn pseudo_transaction_voting_enabled(options: AppRclConsensusOptions, mode: ConsensusMode) -> bool {
    options.standalone || mode == ConsensusMode::Proposing
}

fn trusted_validation_quorum_reached(validations: usize, quorum: usize) -> bool {
    validations >= quorum
}

fn update_operating_mode_after_accept(
    network_ops_mode_owner: &AppNetworkOpsModeOwner,
    positions: usize,
) {
    if positions == 0 && network_ops_mode_owner.is_full() {
        network_ops_mode_owner.set_operating_mode_with_reason(
            NetworkOpsOperatingMode::Connected,
            "no_consensus_positions",
        );
    }
}

/// Consensus positions are an observation of the current round, not a
/// coordinator lifecycle fact. In particular, a start-valid private network
/// cannot receive a peer proposal until its own validator is allowed to
/// propose; interpreting that absence as `Blocked` makes `Full -> Connected`
/// self-fulfilling. The acquisition coordinator must instead receive an
/// explicit peer-health or blocked-state fact from its owning service.
fn coordinator_should_report_no_consensus_positions(positions: usize, _peer_count: usize) -> bool {
    positions == 0
}

fn validation_recovery_conflicts_with_parent(
    recovery: Option<(Uint256, u32)>,
    parent: Uint256,
) -> bool {
    recovery.is_some_and(|(hash, _)| hash != parent)
}

fn retain_stable_recovery_preference(
    ordinary_preferred: Uint256,
    local_parent: Uint256,
    stable_recovery: Option<(Uint256, u32)>,
) -> Uint256 {
    stable_recovery
        .map(|(hash, _)| hash)
        .filter(|hash| *hash != local_parent)
        .unwrap_or(ordinary_preferred)
}

/// The open-ledger view consensus reads current (not-yet-consensus-agreed)
/// transactions from, and resets once a round is accepted.
pub trait RclConsensusOpenLedgerSource {
    fn current_open_transactions(&self) -> Vec<Arc<protocol::STTx>>;
    fn has_open_transactions(&self) -> bool;
    fn accept_consensus_ledger(
        &self,
        next_seq: u32,
        base_fee: u64,
        parent_hash: &Uint256,
        parent_close_time: u32,
        close_time_resolution: u8,
        completed_transaction_ids: &std::collections::HashSet<Uint256>,
        retry_transactions: &[Arc<protocol::STTx>],
        retries_first: bool,
    );
}

/// The validation-tracking surface the adaptor needs to answer
/// `proposers_validated`/`proposers_finished`/`get_prev_ledger`.
pub trait RclConsensusValidationSource {
    fn num_trusted_for_ledger(&self, ledger_id: Uint256) -> usize;
    fn get_nodes_after(
        &self,
        ledger: &crate::consensus::rcl_validation::RclValidatedLedger,
        ledger_id: &Uint256,
    ) -> usize;
    fn preferred_lcl(
        &self,
        lcl: &crate::consensus::rcl_validation::RclValidatedLedger,
        min_seq: u32,
        peer_counts: &std::collections::BTreeMap<Uint256, u32>,
    ) -> Uint256;
    fn preferred_min_seq(
        &self,
        curr: &crate::consensus::rcl_validation::RclValidatedLedger,
        min_valid_seq: u32,
    ) -> Uint256;
}

impl RclConsensusValidationSource for SharedAppValidations<SystemTimeKeeperClock> {
    fn num_trusted_for_ledger(&self, ledger_id: Uint256) -> usize {
        SharedAppValidations::num_trusted_for_ledger(self, ledger_id)
    }

    fn get_nodes_after(
        &self,
        ledger: &crate::consensus::rcl_validation::RclValidatedLedger,
        ledger_id: &Uint256,
    ) -> usize {
        self.validations()
            .lock()
            .expect("shared app validations mutex must not be poisoned")
            .get_nodes_after(ledger, ledger_id)
    }

    fn preferred_lcl(
        &self,
        lcl: &crate::consensus::rcl_validation::RclValidatedLedger,
        min_seq: u32,
        peer_counts: &std::collections::BTreeMap<Uint256, u32>,
    ) -> Uint256 {
        let decision = self
            .validations()
            .lock()
            .expect("shared app validations mutex must not be poisoned")
            .get_preferred_lcl_diagnostic(lcl, min_seq, peer_counts);
        // Bounded causal record for the preferred-LCL boundary. This exposes
        // whether an unstable target comes from trusted validation support,
        // pending acquisition support, or peer-status fallback without
        // changing the reference-compatible selection.
        tracing::info!(
            target: "lcl_trace",
            event = "preferred_lcl_selected",
            local_lcl_hash = %lcl.id(),
            local_lcl_seq = lcl.seq(),
            min_valid_seq = min_seq,
            selected_hash = %decision.selected,
            selection_source = ?decision.selection_source,
            working_source = ?decision.working_source,
            trie_preferred = ?decision.trie_preferred,
            acquiring_preferred = ?decision.acquiring_preferred,
            validation_recovery_candidate = ?decision.validation_recovery_candidate,
            validation_recovery_support = ?decision.validation_recovery_support,
            validation_recovery_peer_support = ?decision.validation_recovery_peer_support,
            peer_preferred = ?decision.peer_preferred,
            peer_lcl_entry_count = decision.peer_lcl_entry_count,
            trusted_full_validations = decision.current_trusted_full_count,
            acquiring_entry_count = decision.acquiring_entry_count,
            acquiring_waiter_count = decision.acquiring_waiter_count,
            "LCL trace: preferred LCL selected"
        );
        decision.selected
    }

    fn preferred_min_seq(
        &self,
        curr: &crate::consensus::rcl_validation::RclValidatedLedger,
        min_valid_seq: u32,
    ) -> Uint256 {
        self.validations()
            .lock()
            .expect("shared app validations mutex must not be poisoned")
            .get_preferred_min_seq(curr, min_valid_seq)
    }
}

/// Timing and mode overrides for [`AppRclConsensusAdaptor`].
#[derive(Debug, Clone, Copy, Default)]
pub struct AppRclConsensusOptions {
    pub standalone: bool,
    #[allow(dead_code)]
    pub close_time_resolution_override: Option<std::time::Duration>,
}

/// A no-op diagnostics sink for [`AppRclConsensusAdaptor`].
#[derive(Debug, Default, Clone, Copy)]
pub struct NullRclConsensusJournal;

/// Diagnostics sink for consensus-round events.
pub trait RclConsensusJournal: Send + Sync {
    fn trace(&self, message: &str);
    fn info(&self, message: &str);
    fn warn(&self, message: &str);
    fn error(&self, message: &str);
}

impl RclConsensusJournal for NullRclConsensusJournal {
    fn trace(&self, _message: &str) {}
    fn info(&self, _message: &str) {}
    fn warn(&self, _message: &str) {}
    fn error(&self, _message: &str) {}
}

/// Peer relay of consensus artifacts.
pub trait RclConsensusRelay: Send + Sync {
    fn relay_proposal(&self, peer_pos: &RclCxPeerPos);
    fn relay_tx_set(&self, set: &consensus::RclTxSet);
    fn relay_disputed_tx(&self, tx: &consensus::RclCxTxRef);
}

fn disputed_relay_envelope(
    raw_transaction: Vec<u8>,
    local_timestamp: u64,
) -> overlay::TmTransaction {
    overlay::TmTransaction {
        raw_transaction,
        // xrpl.proto TransactionStatus::tsNEW = 1. TmTransaction exposes
        // this generated enum field as an i32 in the current overlay API.
        status: 1,
        receive_timestamp: Some(local_timestamp),
        deferred: None,
    }
}

/// The concrete peer-relay implementation.
pub struct AppRclConsensusRelay {
    overlay: Option<Arc<overlay::runtime::overlay_impl::OverlayImpl>>,
    inbound_transactions: AppInboundTransactions,
    time_keeper: Arc<TimeKeeper<SystemTimeKeeperClock>>,
    validator_keys: ValidatorKeys,
    journal: Arc<dyn RclConsensusJournal>,
}

impl AppRclConsensusRelay {
    pub fn from_application_root(
        root: &ApplicationRoot,
        inbound_transactions: AppInboundTransactions,
        validator_keys: ValidatorKeys,
        journal: impl RclConsensusJournal + 'static,
    ) -> Self {
        Self {
            overlay: root.overlay_runtime().map(|rt| rt.overlay()),
            inbound_transactions,
            time_keeper: root.shared_time_keeper(),
            validator_keys,
            journal: Arc::new(journal),
        }
    }

    pub fn validator_keys(&self) -> &ValidatorKeys {
        &self.validator_keys
    }
}

impl RclConsensusRelay for AppRclConsensusRelay {
    fn relay_proposal(&self, peer_pos: &RclCxPeerPos) {
        let Some(overlay) = self.overlay.as_ref() else {
            self.journal
                .trace("relay_proposal: no overlay attached, skipping broadcast");
            return;
        };

        let proposal = peer_pos.proposal();
        let message = overlay::TmProposeSet {
            propose_seq: proposal.propose_seq(),
            current_tx_hash: proposal.position().data().to_vec(),
            node_pub_key: peer_pos.public_key().as_bytes().to_vec(),
            close_time: proposal.close_time().as_seconds(),
            signature: peer_pos.signature().to_vec(),
            previousledger: proposal.prev_ledger().data().to_vec(),
            added_transactions: Vec::new(),
            removed_transactions: Vec::new(),
            ..Default::default()
        };

        let _ = overlay.relay_proposal(message, peer_pos.suppression_id(), *peer_pos.public_key());
    }

    fn relay_tx_set(&self, set: &consensus::RclTxSet) {
        use overlay::Overlay;

        let set_id = consensus::ConsensusTxSet::id(set);
        {
            let sync_tree = set.to_sync_tree();
            let mut guard = self
                .inbound_transactions
                .lock()
                .expect("inbound_transactions mutex");
            guard.give_set(set_id, std::sync::Arc::new(sync_tree), false);
        }

        // rippled's `InboundTransactions::giveSet` synchronously invokes
        // NetworkOPs::mapComplete, which broadcasts TMHaveSet before the
        // matching proposal can make a peer create an acquisition. Our
        // acquired-set completion crosses an owner-strand channel, so local
        // consensus sets must announce here instead; otherwise the peer can
        // snapshot an empty set of serving peers and miss this proposal round.
        if let Some(overlay) = self.overlay.as_ref() {
            let message = overlay::ProtocolMessage::new(overlay::ProtocolPayload::HaveSet(
                overlay::TmHaveTransactionSet {
                    status: 1, // protocol::tsHAVE
                    hash: set_id.data().to_vec(),
                },
            ));
            overlay.broadcast(&message);
        } else {
            self.journal
                .trace("relay_tx_set: no overlay attached, skipping availability broadcast");
        }
    }

    fn relay_disputed_tx(&self, tx: &consensus::RclCxTxRef) {
        let Some(overlay) = self.overlay.as_ref() else {
            self.journal
                .trace("relay_disputed_tx: no overlay attached, skipping broadcast");
            return;
        };

        // Disputed transactions are a new local relay, not a replay of the
        // untrusted TMTransaction envelope that originally delivered them.
        let message = disputed_relay_envelope(
            tx.item().data().to_vec(),
            self.time_keeper.now().as_seconds() as u64,
        );
        overlay.relay_transaction(tx.id(), Some(message), &std::collections::BTreeSet::new());
    }
}

/// Work captured by `on_accept` that must execute synchronously on the
/// consensus strand, matching rippled's single-threaded
/// `doAccept → endConsensus → beginConsensus` call chain.
pub struct PendingAcceptWork {
    /// Exact `prevLedger` used by the consensus round. The asynchronous accept
    /// job must build on this snapshot, never on a moving global closed LCL.
    pub parent_ledger: Arc<ledger::Ledger>,
    pub closed_seq: u32,
    pub close_time: u32,
    pub close_resolution: u8,
    pub correct_close_time: bool,
    /// Offset computed from close-time votes. Rippled applies it only after
    /// switchLCL, so Quaxar carries it through the handoff instead of
    /// adjusting during on_accept.
    pub close_time_adjustment_seconds: Option<i64>,
    /// Hash of the consensus transaction set that built this ledger.
    pub consensus_hash: Uint256,
    /// `false` means consensus accepted while on a wrong LCL, so the
    /// outward status event must be `neLOST_SYNC`.
    pub have_correct_lcl: bool,
    pub consensus_succeeded: bool,
    pub base_fee_drops: u64,
    /// Disputes we voted "no" on, carried to the next open ledger exactly as
    /// rippled inserts rejected non-pseudo disputes into retriableTxs.
    pub rejected_dispute_retries: Vec<Arc<protocol::STTx>>,
    pub txns: Vec<Arc<protocol::STTx>>,
    pub validation: Option<crate::state::application_root::PendingValidation>,
}

pub struct AppRclConsensusAdaptor {
    options: AppRclConsensusOptions,
    time_keeper: Arc<TimeKeeper<SystemTimeKeeperClock>>,
    ledger_master_runtime: Arc<AppLedgerMasterRuntime>,
    open_ledger: SharedAppOpenLedger,
    validations: SharedAppValidations<SystemTimeKeeperClock>,
    app_root: crate::state::application_root::ApplicationRoot,
    pub(crate) validators: Arc<ValidatorList>,
    #[allow(dead_code)]
    pub(crate) network_ops_mode_owner: AppNetworkOpsModeOwner,
    ledger_acceptor: Arc<dyn LedgerAcceptor>,
    inbound_transactions: AppInboundTransactions,
    transaction_master: Arc<TransactionMaster>,
    relay: AppRclConsensusRelay,
    journal: Arc<dyn RclConsensusJournal>,
    pub(crate) validator_keys: ValidatorKeys,
    /// Mirrors rippled RCLConsensus::Adaptor::validating_. Recomputed for
    /// every round from keys, restart protection, blocked state and UNL
    /// expiry; doAccept may subsequently clear it for an incompatible child.
    validating: AtomicBool,
    /// Matches rippled `valCookie_`: one non-zero cookie per adaptor, reused
    /// for every local validation rather than regenerated per ledger.
    val_cookie: u64,
    /// Matches rippled `lastValidationTime_`: validation timestamps never go
    /// backward even if the close clock pauses or adjusts.
    last_validation_time: AtomicU32,
    /// Mirrors rippled RCLCensorshipDetector: tracks transaction IDs proposed
    /// in correct-LCL rounds and warns when eligible IDs remain excluded.
    censorship_detector: StdMutex<CensorshipDetector<Uint256, u32>>,
    fee_vote: Option<Arc<FeeVote>>,
    negative_unl_vote: Option<Arc<crate::amendments::negative_unl_vote::NegativeUNLVote>>,
    amendment_status: Option<Arc<crate::amendments::amendment_status::AmendmentStatus>>,
    #[allow(dead_code)]
    overlay: Option<Arc<overlay::runtime::overlay_impl::OverlayImpl>>,
    parms: ConsensusParms,
    tx_set_cache: consensus::rcl::RclTxSetSharedCache,
    /// Accept-work captured by `on_accept` for synchronous execution by
    /// the strand thread. In the single-strand model, this is read
    /// immediately after `timer_entry` returns on the same thread.
    /// Uses a Mutex to satisfy the type system (ConsensusAdaptor::on_accept
    /// takes &self), but only one thread ever accesses this.
    pub(crate) pending_accept: StdMutex<Option<PendingAcceptWork>>,
    /// Ledger most recently requested by consensus after a cache miss.
    ///
    /// This mirrors rippled's `acquiringLedger_`: consensus may ask for the
    /// same unavailable LCL on every timer/proposal pass, but only the first
    /// miss should begin its potentially expensive inbound acquisition. When
    /// coordinator capacity is occupied, its typed disposition retains the
    /// latest preferred-LCL demand and its exact app origin; this latch remains
    /// set because the coordinator, not a later consensus callback, owns the
    /// eventual replay. See `CoordinatorRunner::has_deferred_consensus_target`.
    acquiring_ledger: StdMutex<Option<Uint256>>,
}

#[allow(clippy::too_many_arguments)]
impl AppRclConsensusAdaptor {
    pub fn new(
        options: AppRclConsensusOptions,
        time_keeper: Arc<TimeKeeper<SystemTimeKeeperClock>>,
        ledger_master_runtime: Arc<AppLedgerMasterRuntime>,
        open_ledger: SharedAppOpenLedger,
        validations: SharedAppValidations<SystemTimeKeeperClock>,
        validators: Arc<ValidatorList>,
        network_ops_mode_owner: AppNetworkOpsModeOwner,
        ledger_acceptor: Arc<dyn LedgerAcceptor>,
        inbound_transactions: AppInboundTransactions,
        transaction_master: Arc<TransactionMaster>,
        relay: AppRclConsensusRelay,
        journal: impl RclConsensusJournal + 'static,
        validator_keys: ValidatorKeys,
        fee_vote: Option<Arc<FeeVote>>,
        negative_unl_vote: Option<Arc<crate::amendments::negative_unl_vote::NegativeUNLVote>>,
        amendment_status: Option<Arc<crate::amendments::amendment_status::AmendmentStatus>>,
        overlay: Option<Arc<overlay::runtime::overlay_impl::OverlayImpl>>,
        app_root: crate::state::application_root::ApplicationRoot,
    ) -> Self {
        let tx_set_cache: consensus::rcl::RclTxSetSharedCache =
            Arc::new(shamap::tree_node_cache::TreeNodeCache::new(
                "consensus-tx-set-cache",
                256,
                time::Duration::minutes(5),
                basics::tagged_cache::MonotonicClock::default(),
            ));
        Self {
            options,
            time_keeper,
            ledger_master_runtime,
            open_ledger,
            validations,
            app_root,
            validators,
            network_ops_mode_owner,
            ledger_acceptor,
            inbound_transactions,
            transaction_master,
            relay,
            journal: Arc::new(journal),
            validator_keys,
            validating: AtomicBool::new(false),
            val_cookie: {
                let cookie = basics::random::rand_int_full::<u64>();
                if cookie == 0 { 1 } else { cookie }
            },
            last_validation_time: AtomicU32::new(0),
            censorship_detector: StdMutex::new(CensorshipDetector::new()),
            fee_vote,
            negative_unl_vote,
            amendment_status,
            overlay,
            parms: ConsensusParms::default(),
            tx_set_cache,
            pending_accept: StdMutex::new(None),
            acquiring_ledger: StdMutex::new(None),
        }
    }

    #[allow(dead_code)]
    fn now(&self) -> NetClockTimePoint {
        self.time_keeper.close_time()
    }

    pub fn is_validator(&self) -> bool {
        self.validator_keys.keys.is_some()
    }

    fn is_validating(&self) -> bool {
        self.validating.load(Ordering::Acquire)
    }

    /// Mirrors rippled `RCLConsensus::Adaptor::preStartRound`: a key alone
    /// is insufficient to validate. Restart protection, amendment/UNL block,
    /// and configured-list expiry must all allow local validation.
    fn update_validating_for_round(&self, prev_ledger: &RclCxLedger) -> bool {
        let root = &self.app_root;
        let now = root.current_network_time_seconds();
        let expired_unl = !self.options.standalone
            && self.validators.count() != 0
            && self.validators.expires().is_none_or(|expiry| expiry < now);
        if expired_unl {
            tracing::error!(target: "consensus",
                "Voluntarily bowing out of consensus because validator list is expired");
        }
        let validating = Self::round_validation_eligible(
            self.validator_keys.keys.is_some(),
            prev_ledger.seq(),
            root.max_disallowed_ledger(),
            self.network_ops_mode_owner.is_blocked(),
            self.options.standalone,
            self.validators.count(),
            self.validators.expires(),
            now,
        );

        self.validating.store(validating, Ordering::Release);
        validating
    }

    fn next_validation_time(&self) -> u32 {
        let candidate = self.time_keeper.close_time().as_seconds();
        loop {
            let last = self.last_validation_time.load(Ordering::Acquire);
            let next = candidate.max(last.saturating_add(1));
            if self
                .last_validation_time
                .compare_exchange(last, next, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                return next;
            }
        }
    }

    fn clear_validating_if_incompatible(
        &self,
        built: &ledger::Ledger,
        consensus_tx_set: Uint256,
        accepted_transactions: &[Arc<protocol::STTx>],
    ) {
        let ledger_master = self.ledger_master_runtime.ledger_master();
        let compatibility = ledger_master.compatibility_audit(built);
        if self.is_validating() && !compatibility.compatible() {
            // This path is exceptional and the locally-built child will often
            // be evicted before an operator can inspect it. Keep the complete
            // consensus input identity here so a later canonical comparison
            // can distinguish a transaction-set/proposal divergence from a
            // transaction-execution or metadata divergence.
            let accepted_tx_ids = accepted_transactions
                .iter()
                .map(|tx| tx.get_transaction_id())
                .collect::<Vec<_>>();
            let accepted_tx_metadata = accepted_transactions
                .iter()
                .filter_map(|tx| {
                    let tx_id = tx.get_transaction_id();
                    let (_, mut metadata) = built.tx_read(tx_id).ok()??;
                    let result = metadata.get_result_ter();
                    let index = metadata.get_index();
                    let mut serialized = protocol::Serializer::default();
                    metadata.add_raw(&mut serialized, result, index);
                    Some((
                        tx_id,
                        result.to_int(),
                        index,
                        basics::str_hex::str_hex(serialized.data()),
                    ))
                })
                .collect::<Vec<_>>();
            tracing::warn!(
                target: "consensus",
                seq = built.header().seq,
                child_hash = %built.header().hash,
                parent_hash = %built.header().parent_hash,
                transaction_root = %built.header().tx_hash,
                state_root = %built.header().account_hash,
                consensus_tx_set = %consensus_tx_set,
                accepted_tx_ids = ?accepted_tx_ids,
                accepted_tx_metadata = ?accepted_tx_metadata,
                compatibility = ?compatibility,
                "Not validating incompatible consensus child"
            );
            self.validating.store(false, Ordering::Release);
        }
    }

    fn validated_view(
        &self,
        ledger: &RclCxLedger,
    ) -> crate::consensus::rcl_validation::RclValidatedLedger {
        crate::consensus::rcl_validation::RclValidatedLedger::from_ledger(&ledger.ledger())
    }

    fn round_validation_eligible(
        has_keys: bool,
        prev_ledger_seq: u32,
        max_disallowed_ledger: u32,
        blocked: bool,
        standalone: bool,
        configured_validator_count: usize,
        expires: Option<u32>,
        now: u32,
    ) -> bool {
        if !has_keys || prev_ledger_seq < max_disallowed_ledger || blocked {
            return false;
        }
        standalone || configured_validator_count == 0 || expires.is_some_and(|expiry| expiry >= now)
    }

    fn sync_tree_to_rcl_tx_set(&self, sync_tree: &shamap::sync::SyncTree) -> consensus::RclTxSet {
        sync_tree_to_rcl_tx_set(sync_tree, &self.tx_set_cache)
    }

    pub fn tx_set_cache(&self) -> &consensus::rcl::RclTxSetSharedCache {
        &self.tx_set_cache
    }
}

fn sync_tree_to_rcl_tx_set(
    sync_tree: &shamap::sync::SyncTree,
    cache: &consensus::rcl::RclTxSetSharedCache,
) -> consensus::RclTxSet {
    consensus::RclTxSet::from_parts(sync_tree.root(), Arc::clone(cache), sync_tree.backed(), 0)
}

/// A resolver-visible inbound ledger is not a consensus parent until its
/// exact Worker 2 acquisition identity passes the durable fence. Returning it
/// from `acquire_ledger` would let `handleWrongLedger` start a replacement
/// round before NetworkOPs can apply its LCL transition gate.
fn resolved_consensus_ledger_is_adoptable(provisional: bool) -> bool {
    !provisional
}

fn should_acquire_consensus_ledger(
    acquiring_ledger: &mut Option<Uint256>,
    ledger_id: Uint256,
) -> bool {
    if *acquiring_ledger == Some(ledger_id) {
        return false;
    }
    *acquiring_ledger = Some(ledger_id);
    true
}

/// Match `RCLConsensus::Adaptor::acquireLedger`: once generic WrongLedger
/// recovery resolves its target, age inbound transaction-set work to that
/// target's sequence before the consensus engine replays cached proposals.
///
/// The ordinary strand-owned starts already call `new_round`; this is the
/// missing generic `handleWrongLedger -> acquire_ledger -> start_round_internal`
/// path, which bypasses those strand call sites.
fn reset_inbound_transactions_for_resolved_consensus_ledger(
    inbound_transactions: &AppInboundTransactions,
    ledger_seq: u32,
) {
    if let Ok(mut inbound) = inbound_transactions.lock() {
        inbound.new_round(ledger_seq);
    }
}

/// Thin adapter bridging `Validations<RclValidationsAdaptor>` (our inner type)
/// to the `NegativeUNLVoteValidations` trait expected by
/// `NegativeUNLVote::do_voting`. Acquires no additional locks — the caller
/// must already hold the validations mutex.
struct NegativeUNLValidationsAdapter<'a>(
    &'a mut crate::consensus::rcl_validations::RclValidationsInner,
);

impl crate::amendments::negative_unl_vote::NegativeUNLVoteValidations
    for NegativeUNLValidationsAdapter<'_>
{
    fn set_seq_to_keep(&mut self, low: u32, high: u32) {
        self.0.set_seq_to_keep(low, high);
    }

    fn trusted_keys_for_ledger(&mut self, ledger_id: Uint256, seq: u32) -> Vec<PublicKey> {
        self.0
            .get_trusted_for_ledger(&ledger_id, seq)
            .into_iter()
            .map(|wrapped| *wrapped.get_signer_public())
            .collect()
    }
}

impl AppRclConsensusAdaptor {
    /// The shared inbound-ledgers registry if the runtime exposes one. The
    /// acquisition coordinator (when installed) is the single mode writer, so
    /// consensus mode demotions feed typed facts through this registry instead
    /// of writing operating mode directly.
    fn coordinator_inbound(&self) -> Option<Arc<crate::ledger::inbound_ledgers::InboundLedgers>> {
        self.ledger_master_runtime
            .inbound_ledgers
            .lock()
            .ok()
            .and_then(|guard| guard.as_ref().cloned())
    }
}

fn open_ledger_consensus_snapshot(
    cache: consensus::rcl::RclTxSetSharedCache,
    ledger_seq: u32,
    transactions: &[Arc<protocol::STTx>],
) -> consensus::RclTxSet {
    let mut set = consensus::RclTxSet::new(cache, ledger_seq);
    {
        let mut editable = set.mutable_view();
        for tx in transactions {
            editable.insert(&consensus::RclCxTxRef::from_transaction(tx));
        }
        set = editable.freeze();
    }
    set
}

impl consensus::algorithm::ConsensusAdaptor for AppRclConsensusAdaptor {
    type Ledger = RclCxLedger;
    type NodeId = PublicKey;
    type TxSet = consensus::RclTxSet;
    type PeerPos = RclCxPeerPos;

    fn acquire_ledger(&self, ledger_id: &Uint256) -> Option<Self::Ledger> {
        let hash = basics::sha_map_hash::SHAMapHash::new(*ledger_id);
        if let Some(ledger) = self.app_root.resolve_ledger_by_hash(hash) {
            let provisional = self.app_root.inbound_ledger_is_provisional(*ledger_id);
            if resolved_consensus_ledger_is_adoptable(provisional) {
                // rippled RCLConsensus::Adaptor::acquireLedger calls
                // inboundTransactions_.newRound(built->header().seq) before
                // returning a cached target to generic WrongLedger recovery.
                // Unlike normal strand starts, `handleWrongLedger` enters
                // start_round_internal directly, so this reset must live here.
                reset_inbound_transactions_for_resolved_consensus_ledger(
                    &self.inbound_transactions,
                    ledger.header().seq,
                );
                // A resolved ledger is immediately usable by generic WrongLedger
                // recovery. `need_network_ledger` is a startup/publication status
                // flag, not an eligibility gate for an already acquired consensus
                // LCL.
                return Some(RclCxLedger::new(ledger));
            }
            tracing::info!(
                target: "lcl_trace",
                event = "consensus_wrong_ledger_provisional",
                target_hash = %ledger_id,
                candidate_hash = %ledger.header().hash,
                candidate_seq = ledger.header().seq,
                "LCL trace: generic WrongLedger retained exact-target recovery behind durable fence"
            );
        }

        let shared = self
            .ledger_master_runtime
            .inbound_ledgers
            .lock()
            .ok()
            .and_then(|guard| guard.as_ref().cloned());
        if let Some(shared) = shared {
            let should_acquire = should_acquire_consensus_ledger(
                &mut self
                    .acquiring_ledger
                    .lock()
                    .expect("acquiring_ledger mutex must not be poisoned"),
                *ledger_id,
            );
            if should_acquire {
                // Match rippled RCLConsensus::Adaptor::acquireLedger: start
                // cache-miss recovery through a JtAdvance "GetConsL1" job so
                // consensus timer/proposal processing does not perform peer
                // request setup inline.
                let requested_hash = *ledger_id;
                let _ =
                    self.app_root
                        .job_queue()
                        .add_job(JobType::JtAdvance, "GetConsL1", move || {
                            shared.acquire_closed_ledger_async(
                                requested_hash,
                                crate::ledger::inbound_ledgers::AcquireReason::Consensus,
                            );
                        });
            }
        }
        None
    }

    fn acquire_tx_set(&self, set_id: &Uint256) -> Option<Self::TxSet> {
        let sync_tree = {
            let mut guard = self
                .inbound_transactions
                .lock()
                .expect("inbound transactions mutex must not be poisoned");
            guard.get_set(*set_id, true)?
        };
        Some(self.sync_tree_to_rcl_tx_set(&sync_tree))
    }

    fn has_open_transactions(&self) -> bool {
        RclConsensusOpenLedgerSource::has_open_transactions(&self.open_ledger)
    }

    fn proposers_validated(&self, prev_ledger: &Uint256) -> usize {
        RclConsensusValidationSource::num_trusted_for_ledger(&self.validations, *prev_ledger)
    }

    fn proposers_finished(&self, prev_ledger: &Self::Ledger, prev_ledger_id: &Uint256) -> usize {
        let wrapped = self.validated_view(prev_ledger);
        RclConsensusValidationSource::get_nodes_after(&self.validations, &wrapped, prev_ledger_id)
    }

    fn get_prev_ledger(
        &self,
        prev_ledger_id: &Uint256,
        prev_ledger: &Self::Ledger,
        mode: ConsensusMode,
    ) -> Uint256 {
        let min_valid_seq = self
            .ledger_master_runtime
            .ledger_master()
            .valid_ledger_seq();
        let wrapped = self.validated_view(prev_ledger);
        let ordinary_preferred = RclConsensusValidationSource::preferred_min_seq(
            &self.validations,
            &wrapped,
            min_valid_seq,
        );
        // A validation-recovery candidate is moving advice, but once the
        // coordinator binds its provenance-backed anchor it is the exact
        // GetConsL1 target. Retain it across timer checks until lifecycle
        // reconciliation clears it; otherwise the trie-local preference can
        // redirect generic consensus back onto the stale local branch.
        let stable_recovery_anchor = self
            .coordinator_inbound()
            .and_then(|inbound| inbound.coordinator_validation_recovery_latch().0);
        let preferred = retain_stable_recovery_preference(
            ordinary_preferred,
            prev_ledger.id(),
            stable_recovery_anchor,
        );
        if mode != ConsensusMode::WrongLedger && preferred != *prev_ledger_id {
            // rippled RCLConsensus.cpp:313-316: consensusViewChange() demotes
            // FULL/TRACKING→CONNECTED when the preferred ledger diverges.
            let current_mode = self.app_root.network_ops_operating_mode();
            let preferred_resident = self
                .app_root
                .resolve_ledger_by_hash(basics::sha_map_hash::SHAMapHash::new(preferred))
                .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
            let local_closed = self.app_root.closed_ledger().map(|ledger| {
                (
                    *ledger.header().hash.as_uint256(),
                    ledger.header().seq,
                    ledger.header().close_time,
                )
            });
            let published_ledger = self
                .app_root
                .published_ledger()
                .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
            let validated_anchor = self
                .ledger_master_runtime
                .ledger_master()
                .validated_ledger()
                .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
            let last_valid_anchor = self
                .ledger_master_runtime
                .ledger_master()
                .last_valid_ledger();
            let previous_ledger = (
                *prev_ledger.ledger().header().hash.as_uint256(),
                prev_ledger.ledger().header().seq,
                prev_ledger.ledger().header().close_time,
            );
            if current_mode == crate::NetworkOpsOperatingMode::Full
                || current_mode == crate::NetworkOpsOperatingMode::Tracking
            {
                tracing::info!(
                    target: "consensus",
                    event = "consensus_view_change_demotion",
                    ?current_mode,
                    consensus_mode = ?mode,
                    min_valid_seq,
                    requested = %prev_ledger_id,
                    previous_ledger = ?previous_ledger,
                    preferred = %preferred,
                    preferred_resident = ?preferred_resident,
                    local_closed = ?local_closed,
                    published_ledger = ?published_ledger,
                    validated_anchor = ?validated_anchor,
                    last_valid_anchor = ?last_valid_anchor,
                    live_current_ledger_index = ?self.app_root.live_current_ledger_index(),
                    "consensusViewChange: demoting to Connected (preferred ledger differs)"
                );
                // Coordinator mode: the coordinator is the single mode writer.
                // Feed rippled's mode-only consensusViewChange fact (demotes
                // Tracking/Full -> Connected without selecting an acquisition
                // target) and let the coordinator publish. The serialized
                // checkLastClosedLedger path owns target-bearing divergence.
                if let Some(coordinator) = self.coordinator_inbound()
                    && coordinator.coordinator_installed()
                {
                    coordinator.coordinator_consensus_view_change();
                } else {
                    self.app_root.set_network_ops_operating_mode_with_reason(
                        crate::NetworkOpsOperatingMode::Connected,
                        "preferred_lcl_divergence",
                    );
                }
            } else {
                tracing::info!(
                    target: "consensus",
                    event = "consensus_view_change_mismatch",
                    consensus_mode = ?mode,
                    min_valid_seq,
                    requested = %prev_ledger_id,
                    previous_ledger = ?previous_ledger,
                    preferred = %preferred,
                    preferred_resident = ?preferred_resident,
                    local_closed = ?local_closed,
                    published_ledger = ?published_ledger,
                    validated_anchor = ?validated_anchor,
                    last_valid_anchor = ?last_valid_anchor,
                    live_current_ledger_index = ?self.app_root.live_current_ledger_index(),
                    "Consensus view change — preferred ledger differs from current"
                );
            }
        }
        preferred
    }

    fn on_mode_change(&self, before: ConsensusMode, after: ConsensusMode) {
        self.journal
            .info(&format!("Consensus mode change {before:?} -> {after:?}"));
        // Matches rippled RCLConsensus::Adaptor::onModeChange: leaving a
        // proposing/observing process discards tracked proposals to avoid
        // false censorship warnings after a context change.
        if matches!(before, ConsensusMode::Proposing | ConsensusMode::Observing) && before != after
        {
            self.censorship_detector
                .lock()
                .expect("censorship detector mutex")
                .reset();
        }
    }

    fn on_close(
        &self,
        prev_ledger: &Self::Ledger,
        now: NetClockTimePoint,
        mode: ConsensusMode,
    ) -> consensus::algorithm::consensus::ConsensusResultOf<Self> {
        // Match RCLConsensus::Adaptor::onClose ordering: advertise that we
        // are closing, re-inject held transactions, mark the ledger being
        // built, then take one immutable transaction snapshot under the close
        // gate. This prevents the submission path from interleaving with the
        // snapshot.
        let txs = {
            // Keep the complete close snapshot and any synchronous batch apply
            // behind the same outer transition gate as a preferred-LCL jump.
            // The lock order is always LCL gate, then close gate.
            let _lcl_transition_guard = self.app_root.lcl_transition_gate().lock();
            let _close_guard = self
                .app_root
                .close_gate()
                .lock()
                .expect("close_gate mutex must not be poisoned");
            self.app_root.broadcast_consensus_status_change(
                prev_ledger.ledger().as_ref(),
                1, // neCLOSING_LEDGER
                mode != ConsensusMode::WrongLedger,
            );
            let next_seq = prev_ledger.seq().saturating_add(1);
            self.ledger_master_runtime.set_building_ledger(next_seq);
            let mut run_sync_batch = false;
            let _ = self
                .app_root
                .apply_held_transactions_to_network_ops(SHAMapHash::new(prev_ledger.id()), |_| {
                    run_sync_batch = true
                });
            // rippled's LedgerMaster::applyHeldTransactions calls
            // processTransactionSet only for a non-empty held set. Its sync
            // batch may also consume previously queued work; do the same, but
            // never unconditionally flush normal async peer ingress here.
            if run_sync_batch {
                let _ = self.app_root.apply_network_ops_pending_to_open_ledger();
            }
            RclConsensusOpenLedgerSource::current_open_transactions(&self.open_ledger)
        };
        // close_gate released — batch-apply can resume while we build the set.
        let mut set = open_ledger_consensus_snapshot(
            Arc::clone(&self.tx_set_cache),
            prev_ledger.seq() + 1,
            &txs,
        );
        {
            let mut editable = set.mutable_view();
            // Rippled injects amendment and fee pseudo-transactions after a
            // flag LCL. Negative-UNL voting runs after the preceding voting
            // LCL, for the consensus session that produces the flag ledger.
            if pseudo_transaction_voting_enabled(self.options, mode)
                && prev_ledger.ledger().is_flag_ledger()
            {
                // Amendment voting — creates ttAMENDMENT pseudo-txs for
                // amendments gaining/losing majority or activating.
                if let Some(ref amendment_status) = self.amendment_status {
                    let prev_id = prev_ledger.ledger().header().parent_hash;
                    let parent_validations =
                        self.validations.store().trusted_for_ledger_by_sequence(
                            *prev_id.as_uint256(),
                            prev_ledger.seq() - 1,
                        );
                    let parent_validations = self
                        .validators
                        .negative_unl_filter_validations(parent_validations);
                    let mut vote_set: Vec<protocol::STTx> = Vec::new();
                    if trusted_validation_quorum_reached(
                        parent_validations.len(),
                        self.validators.quorum(),
                    ) {
                        amendment_status.do_voting_for_ledger(
                            &prev_ledger.ledger(),
                            &parent_validations,
                            &mut vote_set,
                        );
                    }
                    for pseudo_tx in &vote_set {
                        editable.insert(&consensus::RclCxTxRef::from_transaction(pseudo_tx));
                    }
                    if !vote_set.is_empty() {
                        tracing::info!(
                            target: "consensus",
                            count = vote_set.len(),
                            "on_close: injected amendment pseudo-transactions"
                        );
                    }
                }

                // FeeVote — injects a ttFEE pseudo-tx when the network
                // should move to new fee parameters.
                if let Some(ref fee_vote) = self.fee_vote {
                    let prev_id = prev_ledger.ledger().header().parent_hash;
                    let parent_validations =
                        self.validations.store().trusted_for_ledger_by_sequence(
                            *prev_id.as_uint256(),
                            prev_ledger.seq() - 1,
                        );
                    let parent_validations = self
                        .validators
                        .negative_unl_filter_validations(parent_validations);
                    let mut fee_vote_set: Vec<protocol::STTx> = Vec::new();
                    let ledger_ref = prev_ledger.ledger();
                    if trusted_validation_quorum_reached(
                        parent_validations.len(),
                        self.validators.quorum(),
                    ) {
                        fee_vote.do_voting(&*ledger_ref, &parent_validations, &mut fee_vote_set);
                    }
                    for pseudo_tx in &fee_vote_set {
                        editable.insert(&consensus::RclCxTxRef::from_transaction(pseudo_tx));
                    }
                    if !fee_vote_set.is_empty() {
                        tracing::info!(
                            target: "consensus",
                            count = fee_vote_set.len(),
                            "on_close: injected fee pseudo-transactions"
                        );
                    }
                }
            } else if pseudo_transaction_voting_enabled(self.options, mode)
                && prev_ledger.ledger().is_voting_ledger()
            {
                // NegativeUNLVote — injects ttUNL_MODIFY pseudo-txs for
                // validator disable/re-enable when reliability thresholds
                // are crossed.
                if let Some(ref neg_unl_vote) = self.negative_unl_vote {
                    let unl_keys = self.validators.get_trusted_master_keys();
                    let mut nunl_vote_set: Vec<protocol::STTx> = Vec::new();
                    // Acquire the validations lock to get mutable access for
                    // NegativeUNLVoteValidations::set_seq_to_keep and
                    // trusted_keys_for_ledger, then release it immediately.
                    {
                        let mut validations_guard = self
                            .validations
                            .validations()
                            .lock()
                            .expect("shared app validations mutex must not be poisoned");
                        let mut adapter = NegativeUNLValidationsAdapter(&mut validations_guard);
                        let ledger_ref = prev_ledger.ledger();
                        neg_unl_vote.do_voting(
                            &*ledger_ref,
                            &unl_keys,
                            &mut adapter,
                            &mut nunl_vote_set,
                        );
                    }
                    for pseudo_tx in &nunl_vote_set {
                        editable.insert(&consensus::RclCxTxRef::from_transaction(pseudo_tx));
                    }
                    if !nunl_vote_set.is_empty() {
                        tracing::info!(
                            target: "consensus",
                            count = nunl_vote_set.len(),
                            "on_close: injected negative-UNL pseudo-transactions"
                        );
                    }
                }
            }

            set = editable.freeze();
        }

        if mode != ConsensusMode::WrongLedger {
            let proposed = set
                .all_items()
                .into_iter()
                .map(|item| TxIDSeq {
                    txid: item.key(),
                    seq: prev_ledger.seq().saturating_add(1),
                })
                .collect();
            self.censorship_detector
                .lock()
                .expect("censorship detector mutex")
                .propose(proposed);
        }

        let position_id = consensus::ConsensusTxSet::id(&set);
        let node_id = self
            .validator_keys
            .keys
            .as_ref()
            .map(|k| k.public_key)
            .unwrap_or_else(|| PublicKey::from_bytes([0u8; 33]));
        let position = Proposal::new(prev_ledger.id(), 0, position_id, now, now, node_id);

        {
            let sync_tree = set.to_sync_tree();
            let mut guard = self
                .inbound_transactions
                .lock()
                .expect("inbound_transactions mutex");
            guard.give_set(position_id, Arc::new(sync_tree), false);
            tracing::info!(
                target: "consensus",
                parent_hash = %prev_ledger.id(),
                parent_seq = prev_ledger.seq(),
                next_seq = prev_ledger.seq().saturating_add(1),
                consensus_mode = ?mode,
                open_tx_count = txs.len(),
                tx_set_id = %position_id,
                proposed_close_time = now.as_seconds(),
                "on_close: captured local next-round transaction set"
            );
        }

        consensus::algorithm::types::ConsensusResult::new(set, position, position_id)
    }

    fn on_accept(
        &self,
        result: &consensus::algorithm::consensus::ConsensusResultOf<Self>,
        prev_ledger: &Self::Ledger,
        close_resolution: StdDuration,
        raw_close_times: &ConsensusCloseTimes,
        mode: ConsensusMode,
    ) {
        let next_seq = prev_ledger.seq() + 1;
        let base_fee = prev_ledger.ledger().fees().base;

        // Consensus transaction-set bytes originate from peers. rippled catches
        // STTx construction failures here, marks that entry failed, and keeps
        // building the remaining canonical set. Do the same before handing
        // acceptance work to the dedicated consensus strand.
        let items = result.txns.all_items();
        let (decoded_txns, malformed_txns) = decode_consensus_accept_transactions(
            result.txns.id(),
            items.iter().map(|item| (item.data().len(), item.data())),
        );
        let txns = decoded_txns
            .into_iter()
            .map(|tx| canonicalize_consensus_transaction(self.transaction_master.as_ref(), tx))
            .collect::<Vec<_>>();
        let canonical_input_order = txns
            .iter()
            .enumerate()
            .map(|(input_position, tx)| {
                (
                    input_position,
                    tx.get_transaction_id(),
                    tx.get_account_id(protocol::get_field_by_symbol("sfAccount")),
                    tx.get_seq_proxy().value(),
                    tx.get_seq_proxy().is_ticket(),
                    tx.get_txn_type(),
                )
            })
            .collect::<Vec<_>>();
        // The complete canonical set can contain every transaction in a busy
        // ledger. It is useful for forensic debugging, but must never be an
        // always-on production journal payload on the consensus path.
        tracing::debug!(
            target: "lcl_audit",
            parent_hash = %prev_ledger.id(),
            parent_seq = prev_ledger.seq(),
            consensus_tx_set = %result.txns.id(),
            canonical_input_order = ?canonical_input_order,
            "LCL_AUDIT accepted consensus canonical input order"
        );
        let malformed_tx_count = malformed_txns.len();
        for (payload_len, message) in malformed_txns {
            tracing::warn!(
                target: "consensus",
                tx_set = %result.txns.id(),
                payload_len,
                %message,
                "discarded malformed consensus transaction"
            );
        }
        if malformed_tx_count > 0 {
            tracing::warn!(
                target: "consensus",
                tx_set = %result.txns.id(),
                malformed_tx_count,
                "consensus transaction set contains malformed entries"
            );
        }
        let decoded_tx_count = txns.len();
        let raw_close_time = result.position.close_time();
        let close_time_correct = raw_close_time != NetClockTimePoint::default();
        let effective_close_time = if !close_time_correct {
            NetClockTimePoint::new(prev_ledger.close_time().as_seconds().saturating_add(1))
        } else {
            let resolution = time::Duration::seconds(close_resolution.as_secs() as i64);
            consensus::algorithm::timing::effective_close_time(
                raw_close_time,
                resolution,
                prev_ledger.close_time(),
            )
        };
        let close_time = effective_close_time.as_seconds();
        let close_resolution_secs = close_resolution.as_secs().min(u8::MAX as u64) as u8;
        let closed_seq = next_seq;
        let consensus_fail = result.state == consensus::algorithm::types::ConsensusState::MovedOn;

        let mut rejected_dispute_set = CanonicalTXSet::new(result.txns.id());
        for dispute in result.disputes.values() {
            if dispute.get_our_vote() {
                continue;
            }
            let item = dispute.tx().item();
            let (decoded, malformed) = decode_consensus_accept_transactions(
                result.txns.id(),
                [(item.data().len(), item.data())],
            );
            if !malformed.is_empty() {
                tracing::debug!(target: "consensus", tx_id = %dispute.id(),
                    "failed to decode rejected dispute for retry");
            }
            for tx in decoded
                .into_iter()
                .map(|tx| canonicalize_consensus_transaction(self.transaction_master.as_ref(), tx))
            {
                if !matches!(
                    tx.get_txn_type(),
                    protocol::TxType::FEE
                        | protocol::TxType::AMENDMENT
                        | protocol::TxType::UNL_MODIFY
                ) {
                    rejected_dispute_set.insert(tx);
                }
            }
        }

        let rejected_dispute_retries = rejected_dispute_set.drain_ordered();

        let pending_validation = (!consensus_fail)
            .then_some(self.validator_keys.keys.as_ref())
            .flatten()
            .map(|keys| crate::state::application_root::PendingValidation {
                public_key: keys.public_key,
                secret_key: keys.secret_key.clone(),
                node_id: protocol::calc_node_id(&keys.public_key),
                consensus_hash: result.txns.id(),
                proposing: mode == ConsensusMode::Proposing,
            });

        let close_time_adjustment_seconds = if (mode == ConsensusMode::Proposing
            || mode == ConsensusMode::Observing)
            && !consensus_fail
        {
            Some(median_close_offset_seconds(raw_close_times))
        } else {
            None
        };

        // Store the accept work in the adaptor's pending_accept field.
        // In the single-strand model, on_accept is called from timer_entry
        // on the strand thread. The strand thread reads pending_accept
        // immediately after timer_entry returns.
        {
            let mut pending = self
                .pending_accept
                .lock()
                .expect("pending_accept mutex must not be poisoned");
            *pending = Some(PendingAcceptWork {
                parent_ledger: prev_ledger.ledger(),
                closed_seq,
                close_time,
                close_resolution: close_resolution_secs,
                correct_close_time: close_time_correct,
                close_time_adjustment_seconds,
                consensus_hash: result.txns.id(),
                have_correct_lcl: mode != ConsensusMode::WrongLedger,
                consensus_succeeded: result.state
                    == consensus::algorithm::types::ConsensusState::Yes,
                base_fee_drops: base_fee,
                rejected_dispute_retries,
                txns,
                validation: pending_validation,
            });
        }
        tracing::info!(
            target: "consensus",
            parent_hash = %prev_ledger.id(),
            parent_seq = prev_ledger.seq(),
            closed_seq,
            consensus_mode = ?mode,
            consensus_state = ?result.state,
            consensus_tx_set = %result.txns.id(),
            consensus_tx_count = items.len(),
            decoded_tx_count,
            raw_close_time = raw_close_time.as_seconds(),
            raw_close_time_self = raw_close_times.self_.as_seconds(),
            raw_close_time_peer_votes = ?raw_close_times.peers,
            effective_close_time = close_time,
            close_resolution_secs,
            close_time_correct,
            "on_accept: captured consensus result for local child"
        );
    }

    fn propose(&self, pos: &consensus::ConsensusProposal<PublicKey, Uint256, Uint256>) {
        let Some(keys) = self.validator_keys.keys.as_ref() else {
            return;
        };
        match sign_proposal(&keys.secret_key, &keys.public_key, pos) {
            Ok((signature, suppression)) => {
                let peer_pos =
                    RclCxPeerPos::new(keys.public_key, signature, suppression, pos.clone());
                self.relay.relay_proposal(&peer_pos);
            }
            Err(err) => self
                .journal
                .error(&format!("propose: signing failed: {err:?}")),
        }
    }

    fn share_peer_position(&self, prop: &Self::PeerPos) {
        self.relay.relay_proposal(prop);
    }

    fn share_tx(&self, tx: &consensus::RclCxTxRef) {
        self.relay.relay_disputed_tx(tx);
    }

    fn share_tx_set(&self, set: &Self::TxSet) {
        self.relay.relay_tx_set(set);
    }

    fn parms(&self) -> &ConsensusParms {
        &self.parms
    }

    fn next_ledger_time_resolution(
        &self,
        previous_resolution: StdDuration,
        previous_agree: bool,
        ledger_seq: u32,
    ) -> StdDuration {
        let previous = time::Duration::seconds(previous_resolution.as_secs() as i64);
        let next = consensus::algorithm::timing::get_next_ledger_time_resolution(
            previous,
            previous_agree,
            ledger_seq,
        );
        StdDuration::from_secs(next.whole_seconds().max(0) as u64)
    }

    fn round_close_time(
        &self,
        raw: NetClockTimePoint,
        resolution: StdDuration,
    ) -> NetClockTimePoint {
        let resolution = time::Duration::seconds(resolution.as_secs() as i64);
        consensus::algorithm::timing::round_close_time(raw, resolution)
    }

    fn valid_ledger_seq(&self) -> u32 {
        self.ledger_master_runtime
            .ledger_master()
            .valid_ledger_seq()
    }

    fn quorum_keys(&self) -> (usize, HashSet<PublicKey>) {
        let (quorum, keys) = self.validators.get_quorum_keys();
        (quorum, keys.into_iter().collect())
    }

    fn laggards(&self, seq: u32, trusted_keys: &mut HashSet<PublicKey>) -> usize {
        // The generic consensus layer deliberately uses its hardened HashSet,
        // while the existing validation tracker predates that boundary and
        // owns a standard HashSet. Preserve rippled's mutating contract by
        // moving all keys into the tracker, then restoring only its remaining
        // (offline) keys to the generic set.
        // The generic layer's hardened set (Xxh3Builder) must rehash into the
        // standard tracker set (RandomState); mem::take cannot bridge the two
        // hashers, so drain-and-recollect is intentional here.
        #[allow(clippy::drain_collect)]
        let mut validation_keys: StdHashSet<_> = trusted_keys.drain().collect();
        let laggards = self
            .validations
            .validations()
            .lock()
            .expect("shared app validations mutex must not be poisoned")
            .laggards(seq, &mut validation_keys);
        trusted_keys.extend(validation_keys);
        laggards
    }

    fn validator(&self) -> bool {
        self.is_validator()
    }

    fn have_validated(&self) -> bool {
        self.ledger_master_runtime.ledger_master().have_validated()
    }

    fn update_operating_mode(&self, positions: usize) {
        if positions == 0 && self.network_ops_mode_owner.is_full() {
            // Coordinator mode: demote `Full -> Connected` through the typed
            // blocked-state fact; the coordinator publishes. Otherwise the
            // legacy write remains.
            if let Some(coordinator) = self.coordinator_inbound()
                && coordinator.coordinator_installed()
            {
                let peer_count = coordinator
                    .coordinator_snapshot()
                    .map_or(0, |snapshot| snapshot.peer_count());
                if coordinator_should_report_no_consensus_positions(positions, peer_count) {
                    coordinator.coordinator_blocked_with_no_target();
                }
                return;
            }
        }
        update_operating_mode_after_accept(&self.network_ops_mode_owner, positions);
    }
}

// ---------------------------------------------------------------------------
// Single-Strand ConsensusRunner
// ---------------------------------------------------------------------------

/// The consensus runner trait for the single-strand model. All methods take
/// `&mut self` because only the strand thread ever calls them — no locks needed.
///
/// This trait exists so `AppConsensus` can be constructed in `application_root.rs`
/// and then moved to the strand thread in `bootstrap.rs`.
pub trait ConsensusRunner: Send {
    /// Process a proposal. Called on the consensus strand.
    fn peer_proposal(&mut self, now: NetClockTimePoint, peer_pos: &RclCxPeerPos) -> bool;

    /// Run the 1s timer tick. Returns PendingAcceptWork if on_accept fired.
    fn timer_tick(&mut self, now: NetClockTimePoint) -> Option<PendingAcceptWork>;

    /// Start a round. Called after ledger build or by initial bootstrap.
    fn start_round(
        &mut self,
        now: NetClockTimePoint,
        prev_ledger_id: Uint256,
        prev_ledger: RclCxLedger,
        proposing: bool,
    );

    /// Notify tx-set acquired.
    fn got_tx_set(&mut self, now: NetClockTimePoint, tx_set: consensus::RclTxSet);

    /// Build the accepted ledger and start the next round.
    /// Called on the strand after timer_tick returns Some(work).
    fn execute_accept(&mut self, now: NetClockTimePoint, work: PendingAcceptWork);

    /// Phase accessor.
    fn phase(&self) -> consensus::algorithm::ConsensusPhase;

    /// Prev ledger id accessor.
    fn prev_ledger_id(&self) -> Uint256;
}

/// Concrete single-strand consensus driver. Owns `Consensus<AppRclConsensusAdaptor>`
/// directly — NO mutex, NO Arc. Lives on the strand thread's stack.
pub struct AppConsensus {
    pub(crate) adaptor: AppRclConsensusAdaptor,
    state: Consensus<AppRclConsensusAdaptor>,
    /// Tracks the trusted validator keys from the previous round so we can
    /// compute `now_untrusted` (keys removed since last round) for start_round.
    /// Matches rippled's dynamic UNL update behavior.
    last_trusted_keys: HashSet<PublicKey>,
}

impl AppConsensus {
    pub fn new(adaptor: AppRclConsensusAdaptor, _parms: ConsensusParms) -> Self {
        Self {
            adaptor,
            state: Consensus::new(),
            last_trusted_keys: HashSet::default(),
        }
    }

    /// Compute the set of validator keys that were trusted in the previous
    /// round but are no longer trusted (i.e. removed from UNL or added to
    /// the negative UNL). Updates `last_trusted_keys` for the next call.
    fn publish_consensus_mode(&self) {
        use crate::network::network_ops::NetworkOpsConsensusMode;

        let mode = match self.state.mode() {
            ConsensusMode::Observing => NetworkOpsConsensusMode::Observing,
            ConsensusMode::Proposing => NetworkOpsConsensusMode::Proposing,
            ConsensusMode::WrongLedger => NetworkOpsConsensusMode::WrongLedger,
            ConsensusMode::SwitchedLedger => NetworkOpsConsensusMode::SwitchedLedger,
        };
        self.adaptor.network_ops_mode_owner.set_consensus_mode(mode);
    }

    fn compute_trust_changes(&mut self) -> (HashSet<PublicKey>, HashSet<PublicKey>) {
        let current_trusted: HashSet<PublicKey> = self
            .adaptor
            .validators
            .get_trusted_master_keys()
            .into_iter()
            .collect();
        // Keys that were in last_trusted but not in current are now untrusted.
        let now_untrusted: HashSet<PublicKey> = self
            .last_trusted_keys
            .difference(&current_trusted)
            .copied()
            .collect();
        let now_trusted: HashSet<PublicKey> = current_trusted
            .difference(&self.last_trusted_keys)
            .copied()
            .collect();
        // Also include keys on the negative UNL.
        let negative_unl = self.adaptor.validators.get_negative_unl();
        let mut combined_untrusted = now_untrusted;
        for key in negative_unl {
            combined_untrusted.insert(key);
        }
        self.last_trusted_keys = current_trusted;
        (combined_untrusted, now_trusted)
    }

    /// Leave the accepted phase after an accepted-ledger candidate could not
    /// be built. The work's parent is the generic consensus engine's exact
    /// `prevLedger`; never replace it with a concurrently-changing global LCL.
    ///
    /// `execute_accept` is invoked only by the strand after `on_accept` has
    /// placed generic consensus in `Accepted`. Starting a round from this
    /// captured parent is therefore the runner-contract-compatible way to
    /// release that phase and keep the NetworkOps loop making progress.
    fn restart_after_failed_candidate_build(
        &mut self,
        now: NetClockTimePoint,
        work: &PendingAcceptWork,
    ) -> bool {
        if self.state.phase() != consensus::algorithm::ConsensusPhase::Accepted {
            tracing::warn!(
                target: "consensus",
                phase = ?self.state.phase(),
                parent_hash = %work.parent_ledger.header().hash,
                parent_seq = work.parent_ledger.header().seq,
                "candidate-build recovery rejected outside the accepted runner phase"
            );
            return false;
        }

        // `timer_tick` normally took this slot before the JtAccept handoff.
        // Clear it defensively so a failed candidate cannot retain stale
        // accept scheduling state if a caller ever aborts that normal path.
        let discarded_pending = self
            .adaptor
            .pending_accept
            .lock()
            .expect("pending_accept mutex must not be poisoned")
            .take()
            .is_some();
        let parent_hash = *work.parent_ledger.header().hash.as_uint256();
        let parent = crate::consensus_ledger_from_ledger(&work.parent_ledger);
        let proposing = self.adaptor.is_validator()
            && !self.adaptor.options.standalone
            && self.adaptor.network_ops_mode_owner.operating_mode()
                == crate::network::network_ops::NetworkOpsOperatingMode::Full;

        self.start_round(now, parent_hash, parent, proposing);
        tracing::warn!(
            target: "consensus",
            parent_hash = %parent_hash,
            parent_seq = work.parent_ledger.header().seq,
            discarded_pending,
            requested_proposing = proposing,
            resulting_phase = ?self.state.phase(),
            "accepted-ledger candidate build failed; restarted consensus on captured parent"
        );
        true
    }

    fn notify_accepted(
        &self,
        root: &crate::state::application_root::ApplicationRoot,
        closed: &Arc<ledger::Ledger>,
        work: &PendingAcceptWork,
    ) {
        root.broadcast_consensus_status_change(
            closed.as_ref(),
            2, // neACCEPTED_LEDGER
            work.have_correct_lcl,
        );
    }

    fn validate_accepted(
        &self,
        root: &crate::state::application_root::ApplicationRoot,
        closed: &Arc<ledger::Ledger>,
        work: &PendingAcceptWork,
    ) {
        // Matches the second half of rippled doAccept: after notification,
        // compatibility clears validating_ before the final validation gate.
        let hdr = closed.header();

        if let Some(pending) = work.validation.as_ref()
            && self.adaptor.is_validating()
            && self
                .adaptor
                .validations
                .validations()
                .lock()
                .expect("validations lock")
                .can_validate_seq(work.closed_seq)
        {
            tracing::info!(target: "consensus", closed_seq = work.closed_seq, proposing = pending.proposing, "execute_accept: signing validation");
            let ledger_hash = *hdr.hash.as_uint256();
            let validation_time = self.adaptor.next_validation_time();
            match protocol::STValidation::new_signed(
                validation_time,
                &pending.public_key,
                pending.node_id,
                &pending.secret_key,
                |v| {
                    v.set_field_h256(protocol::get_field_by_symbol("sfLedgerHash"), ledger_hash);
                    v.set_field_h256(
                        protocol::get_field_by_symbol("sfConsensusHash"),
                        pending.consensus_hash,
                    );
                    v.set_field_u32(
                        protocol::get_field_by_symbol("sfLedgerSequence"),
                        work.closed_seq,
                    );
                    if pending.proposing {
                        v.set_flag(protocol::VF_FULL_VALIDATION);
                    }

                    // Rippled's validate() sees the last fully validated
                    // ledger as it existed before consensusBuilt runs.
                    if let Some(validated) = root.validated_ledger() {
                        v.set_field_h256(
                            protocol::get_field_by_symbol("sfValidatedHash"),
                            *validated.header().hash.as_uint256(),
                        );
                    }
                    v.set_field_u64(
                        protocol::get_field_by_symbol("sfCookie"),
                        self.adaptor.val_cookie,
                    );
                    if closed.is_voting_ledger() {
                        v.set_field_u64(
                            protocol::get_field_by_symbol("sfServerVersion"),
                            protocol::get_encoded_version(),
                        );
                    }
                    let load_fee_track = root.load_fee_track();
                    let fee =
                        std::cmp::max(load_fee_track.local_fee(), load_fee_track.cluster_fee());
                    if fee > load_fee_track.load_base() {
                        v.set_field_u32(protocol::get_field_by_symbol("sfLoadFee"), fee);
                    }
                    if let Some(fee_vote) = self.adaptor.fee_vote.as_ref()
                        && closed.is_voting_ledger()
                    {
                        fee_vote.do_validation(closed.fees(), closed.rules(), v);
                    }
                    if closed.is_voting_ledger() {
                        if let Some(amendment_status) = self.adaptor.amendment_status.as_ref() {
                            amendment_status.do_validation_for_ledger(closed.as_ref(), v);
                        }
                    }
                },
            ) {
                Ok(built_validation) => {
                    self.adaptor
                        .ledger_acceptor
                        .publish_validation(Arc::new(built_validation));
                    tracing::info!(target: "consensus", closed_seq = work.closed_seq, "execute_accept: validation SIGNED and PUBLISHED");
                }
                Err(err) => {
                    tracing::error!(target: "consensus", closed_seq = work.closed_seq, ?err, "synchronous accept: validation signing failed");
                }
            }
        }
    }

    /// Execute the accept-ledger work and start the next consensus round,
    /// matching rippled's single-threaded flow:
    ///   doAccept (build ledger) → endConsensus (checkLastClosedLedger) →
    ///   beginConsensus (start_round)
    fn do_accept_and_start_next_round(&mut self, now: NetClockTimePoint, work: PendingAcceptWork) {
        let closed_seq = work.closed_seq;
        let root = self.adaptor.app_root.clone();
        let parent_hash = *work.parent_ledger.header().hash.as_uint256();
        let stable_recovery_anchor = self
            .adaptor
            .coordinator_inbound()
            .and_then(|inbound| inbound.coordinator_validation_recovery_latch().0);
        if validation_recovery_conflicts_with_parent(stable_recovery_anchor, parent_hash) {
            let (target_hash, target_seq) =
                stable_recovery_anchor.expect("conflict requires a stable recovery anchor");
            // The round may have entered Accepted before the asynchronous
            // validation recovery became stable. Discard the captured child
            // before any build, store, broadcast, validation, open-ledger
            // rebuild, or LCL mutation can extend the stale branch. Keep the
            // runner Accepted: the NetworkOps strand consumes this handoff and
            // immediately runs its sole endConsensus reconciliation owner,
            // which demotes on the exact target and starts WrongLedger.
            root.notify_consensus_event();
            tracing::warn!(
                target: "lcl_audit",
                work_parent_hash = %parent_hash,
                work_parent_seq = work.parent_ledger.header().seq,
                recovery_target_hash = %target_hash,
                recovery_target_seq = target_seq,
                closed_seq,
                "LCL_AUDIT stale accepted child vetoed pending exact endConsensus recovery"
            );
            return;
        }
        // Quaxar's on_closed_ledger schedules a JtBatch that can otherwise
        // race the newly rebased OpenLedger before this accept finishes.
        // This reentrant gate is the local analogue of rippled's master/ledger
        // locks around doAccept/OpenLedger::accept; it serializes writers but
        // deliberately does not reintroduce a global-parent rejection.
        let _lcl_transition_guard = root.lcl_transition_gate().lock();
        tracing::debug!(
            target: "lcl_audit",
            work_parent_hash = %work.parent_ledger.header().hash,
            work_parent_seq = work.parent_ledger.header().seq,
            closed_seq,
            consensus_hash = %work.consensus_hash,
            have_correct_lcl = work.have_correct_lcl,
            validation_pending = work.validation.is_some(),
            "LCL_AUDIT consensus accept work entered"
        );

        let build_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            root.accept_ledger_with_txns_outcome_from_consensus_parent(
                Arc::clone(&work.parent_ledger),
                work.closed_seq,
                work.close_time,
                work.close_resolution,
                work.correct_close_time,
                work.base_fee_drops,
                work.txns.clone(),
            )
        }));
        match build_result {
            Ok(Ok(outcome)) => {
                // Carry the exact child that atomically replaced the captured
                // parent through all post-accept processing. Re-reading the
                // mutable LCL here could attach this consensus result to a
                // later validation/acquisition switch.
                let closed = root.store_consensus_ledger(Arc::clone(&outcome.closed));
                tracing::info!(
                    target: "lcl_audit",
                    work_parent_hash = %work.parent_ledger.header().hash,
                    work_parent_seq = work.parent_ledger.header().seq,
                    closed_hash = %closed.header().hash,
                    closed_seq = closed.header().seq,
                    closed_parent_hash = %closed.header().parent_hash,
                    closed_tx_hash = %closed.header().tx_hash,
                    closed_close_time = closed.header().close_time,
                    consensus_tx_set = %work.consensus_hash,
                    accepted_tx_count = work.txns.len(),
                    consensus_mode_correct_lcl = work.have_correct_lcl,
                    consensus_succeeded = work.consensus_succeeded,
                    "LCL_AUDIT local consensus child built"
                );
                let mut retriable_transactions = outcome.retry_transactions.clone();
                self.notify_accepted(&root, &closed, &work);
                if work.have_correct_lcl && work.consensus_succeeded {
                    let accepted = work
                        .txns
                        .iter()
                        .map(|tx| tx.get_transaction_id())
                        .collect::<Vec<_>>();
                    let failed = retriable_transactions
                        .iter()
                        .map(|tx| tx.get_transaction_id())
                        .collect::<StdHashSet<_>>();
                    let current_seq = closed.header().seq;
                    self.adaptor
                        .censorship_detector
                        .lock()
                        .expect("censorship detector mutex")
                        .check(accepted, |tx_id, first_seq| {
                            if failed.contains(tx_id) {
                                return true;
                            }
                            let wait = current_seq.saturating_sub(*first_seq);
                            if wait != 0 && wait % 15 == 0 {
                                tracing::warn!(target: "consensus", tx_id = %tx_id,
                                    first_seq, current_seq,
                                    "Potential censorship: eligible transaction has not been included");
                            }
                            false
                        });
                }
                self.adaptor.clear_validating_if_incompatible(
                    closed.as_ref(),
                    work.consensus_hash,
                    &work.txns,
                );
                self.validate_accepted(&root, &closed, &work);
                root.record_consensus_built_ledger(Arc::clone(&closed), work.consensus_hash);
                // Rippled performs censorshipDetector_.check before adding
                // rejected disputes to retriableTxs, then passes the combined
                // canonical retry set to OpenLedger::accept.
                retriable_transactions.extend(work.rejected_dispute_retries.iter().cloned());
                root.rebuild_open_ledger_after_consensus_with_completed(
                    Arc::clone(&closed),
                    &retriable_transactions,
                    !work.rejected_dispute_retries.is_empty(),
                    &outcome.completed_transaction_ids,
                );
                root.set_status_rpc_current_ledger_index(Some(outcome.next_open_index));
                root.set_status_rpc_queue_report(Some(root.tx_q_rpc_report()));
                // `RCLConsensus::Adaptor::doAccept` reports fee changes only
                // after OpenLedger::accept has installed the new open ledger.
                // Keep the notification on its existing client-fee-change job.
                let _ = root.report_fee_change();

                // Match rippled `doAccept`: after `consensusBuilt` and
                // `OpenLedger::accept`, switch the closed LCL to the built
                // child without a global-parent rejection gate.
                root.install_consensus_child(Arc::clone(&closed));

                if let Some(offset_seconds) = work.close_time_adjustment_seconds {
                    let new_offset = self
                        .adaptor
                        .time_keeper
                        .adjust_close_time(time::Duration::seconds(offset_seconds));
                    tracing::debug!(
                        target: "consensus",
                        computed_offset_seconds = offset_seconds,
                        new_close_offset_seconds = new_offset.whole_seconds(),
                        "close_time_adjust"
                    );
                }

                // Do not clear NetworkOps' pending queue here. It may contain
                // submissions accepted after `on_close` captured the prior
                // open-ledger snapshot; clearing it would silently drop those
                // transactions instead of applying them to the new open ledger.
                // The normal batch scheduler owns their subsequent application.

                // The NetworkOps strand is the sole owner of the
                // checkLastClosedLedger/endConsensus policy and of the
                // subsequent round transition. Leave generic consensus in
                // Accepted so that owner observes this exact accepted LCL.
                root.notify_consensus_event();
            }
            Ok(Err(err)) => {
                tracing::error!(target: "consensus", closed_seq, ?err,
                    "accepted-ledger candidate build failed; discarding uninstalled candidate");
                let _ = self.restart_after_failed_candidate_build(now, &work);
            }
            Err(payload) => {
                let message = panic_payload_message(payload);
                tracing::error!(
                    target: "consensus",
                    closed_seq,
                    %message,
                    "accepted-ledger candidate build panicked; discarding uninstalled candidate and preserving NetworkOps strand"
                );
                let _ = self.restart_after_failed_candidate_build(now, &work);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AppConsensus, AppRclConsensusAdaptor, AppRclConsensusOptions, AppRclConsensusRelay,
        ConsensusRunner, NullRclConsensusJournal, PendingAcceptWork,
        coordinator_should_report_no_consensus_positions, decode_consensus_accept_transactions,
        disputed_relay_envelope, median_close_offset_seconds, pseudo_transaction_voting_enabled,
        reset_inbound_transactions_for_resolved_consensus_ledger,
        retain_stable_recovery_preference, trusted_validation_quorum_reached,
        update_operating_mode_after_accept, validation_recovery_conflicts_with_parent,
    };
    use crate::ledger::inbound_ledgers::{AcquireReason, InboundLedgers};
    use crate::network::network_ops::{
        AppNetworkOpsModeOwner, NetworkOpsOperatingMode, SharedNetworkOpsState,
    };
    use crate::state::application_root::ApplicationRoot;
    use crate::tx_queue::transaction::TransactionRelayMetadata;
    use crate::validator::validator_keys::ValidatorKeys;
    use basics::base_uint::Uint256;
    use basics::basic_config::BasicConfig;
    use basics::chrono::NetClockTimePoint;
    use basics::hardened_hash::HardenedHashBuilder;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::MonotonicClock;
    use consensus::ConsensusParms;
    use consensus::algorithm::ConsensusPhase;
    use consensus::algorithm::types::{ConsensusCloseTimes, ConsensusMode};
    use ledger::{FetchPackCache, Ledger, LedgerHeader, calculate_ledger_hash};
    use nodestore::{DummyScheduler, ManagerImp, NullJournal, Scheduler};
    use protocol::{AccountID, STAmount, STTx, TxType, get_field_by_symbol};
    use shamap::family::FullBelowCacheImpl;
    use shamap::item::SHAMapItem;
    use shamap::mutation::MutableTree;
    use shamap::sync::{SHAMapType, SyncState, SyncTree};
    use shamap::tree_node::SHAMapNodeType;
    use shamap::tree_node_cache::TreeNodeCache;
    use std::sync::atomic::AtomicBool;
    use std::sync::{Arc, mpsc};
    use std::time::Duration;
    use tempfile::TempDir;

    #[test]
    fn median_close_offset_matches_rippled_lower_weighted_median() {
        let offset = |self_seconds, peer_votes: &[(u32, i32)]| {
            let mut times = ConsensusCloseTimes {
                self_: NetClockTimePoint::new(self_seconds),
                ..ConsensusCloseTimes::default()
            };
            for (seconds, votes) in peer_votes {
                times.peers.insert(NetClockTimePoint::new(*seconds), *votes);
            }
            median_close_offset_seconds(&times)
        };

        assert_eq!(offset(100, &[]), 0, "our sole sample is the median");
        assert_eq!(
            offset(100, &[(120, 1)]),
            0,
            "two samples use rippled's lower median instead of a mean"
        );
        assert_eq!(
            offset(120, &[(100, 1)]),
            -20,
            "the earlier peer sample is the lower median"
        );
        assert_eq!(
            offset(100, &[(90, 2), (110, 1)]),
            -10,
            "peer vote weights participate in the ordered median"
        );
        assert_eq!(
            offset(100, &[(110, 2), (130, 1)]),
            10,
            "the self sample retains exactly one vote"
        );
    }

    #[test]
    fn different_validation_recovery_parent_vetoes_proposing_until_exact_match() {
        let parent = Uint256::from(10);
        assert!(!validation_recovery_conflicts_with_parent(None, parent));
        assert!(!validation_recovery_conflicts_with_parent(
            Some((parent, 10)),
            parent
        ));
        assert!(validation_recovery_conflicts_with_parent(
            Some((Uint256::from(11), 11)),
            parent
        ));
    }

    #[test]
    fn get_prev_retains_stable_anchor_over_local_or_moving_preference() {
        let local = Uint256::from(10);
        let anchor = Uint256::from(20);
        let moving = Uint256::from(30);
        assert_eq!(
            retain_stable_recovery_preference(local, local, Some((anchor, 20))),
            anchor
        );
        assert_eq!(
            retain_stable_recovery_preference(moving, local, Some((anchor, 20))),
            anchor
        );
        assert_eq!(
            retain_stable_recovery_preference(moving, local, None),
            moving
        );
        assert_eq!(
            retain_stable_recovery_preference(moving, local, Some((local, 10))),
            moving
        );
    }

    fn failed_candidate_test_runner(root: &mut ApplicationRoot) -> AppConsensus {
        let ledger_master_runtime = root.attach_default_ledger_master_runtime();
        let relay = AppRclConsensusRelay::from_application_root(
            root,
            root.inbound_transactions().clone(),
            ValidatorKeys::default(),
            NullRclConsensusJournal,
        );
        let adaptor = AppRclConsensusAdaptor::new(
            AppRclConsensusOptions::default(),
            root.shared_time_keeper(),
            ledger_master_runtime,
            root.open_ledger().clone(),
            root.validations().clone(),
            root.validators(),
            root.network_ops_mode_owner(),
            root.clone_ledger_acceptor(),
            root.inbound_transactions().clone(),
            root.transaction_master(),
            relay,
            NullRclConsensusJournal,
            ValidatorKeys::default(),
            None,
            None,
            None,
            None,
            root.clone(),
        );
        AppConsensus::new(adaptor, ConsensusParms::default())
    }

    /// Build a finalized ledger with a real (non-empty) state map so
    /// `LedgerHistory::insert` accepts it. `from_ledger_seq_and_close_time`
    /// leaves an empty state tree whose zero root hash is rejected by history
    /// insertion, so it can never be resolver-visible.
    fn resolvable_immutable_ledger(seq: u32, parent_fill: u8) -> Arc<Ledger> {
        let mut header = LedgerHeader {
            seq,
            parent_hash: SHAMapHash::new(Uint256::from_array([parent_fill; 32])),
            close_time: seq.saturating_add(100),
            close_time_resolution: 30,
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);
        let mut state_tree = MutableTree::new(seq);
        state_tree
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(Uint256::from_u64(u64::from(seq)), vec![parent_fill; 128]),
            )
            .expect("state entry should insert");
        let mut ledger = Ledger::from_maps(
            header,
            SyncTree::from_root_with_type(
                state_tree.root(),
                SHAMapType::State,
                false,
                seq,
                SyncState::Immutable,
            ),
            SyncTree::new_with_type(SHAMapType::Transaction, false, seq),
        );
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    /// Construct an actual resident inbound acquisition and leave it at the
    /// public completion handoff before its durability state is marked complete.
    /// The resolver insertion mirrors bootstrap's `storeLedger` callback; this
    /// test deliberately does not call any acquisition/registry internals.
    fn install_real_provisional_inbound_candidate(
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
                "rcl-provisional-candidate",
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
        // `on_complete` is the public external/sweep completion handoff. The
        // state remains incomplete, so it is exactly the registry's
        // resolver-visible provisional interval.
        inbound.on_complete(hash, Arc::clone(&ledger));
        runtime
            .ledger_master()
            .ledger_history()
            .insert(ledger, false);
        assert!(inbound.is_provisional(&hash));
        assert!(
            root.resolve_ledger_by_hash(basics::sha_map_hash::SHAMapHash::new(hash))
                .is_some()
        );
        (dir, inbound)
    }

    fn failed_candidate_work(parent_ledger: Arc<Ledger>) -> PendingAcceptWork {
        PendingAcceptWork {
            parent_ledger,
            closed_seq: 11,
            close_time: 1_010,
            close_resolution: 30,
            correct_close_time: true,
            close_time_adjustment_seconds: None,
            consensus_hash: Uint256::from_u64(0xBAD),
            have_correct_lcl: true,
            consensus_succeeded: true,
            base_fee_drops: 10,
            rejected_dispute_retries: Vec::new(),
            txns: Vec::new(),
            validation: None,
        }
    }

    fn install_empty_test_coordinator(
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
                "rcl-accept-veto",
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

    #[test]
    fn failed_candidate_build_keeps_parent_and_restarts_from_accepted() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let parent = Arc::new(Ledger::from_ledger_seq_and_close_time(10, 1_000, false));
        let parent_hash = *parent.header().hash.as_uint256();
        root.on_closed_ledger(Arc::clone(&parent));
        let mut runner = failed_candidate_test_runner(&mut root);
        let before = root
            .closed_ledger()
            .expect("parent should remain installed");

        // `Consensus::new` is in Accepted, exactly as it is immediately after
        // `on_accept`; retain a stale work item to prove recovery clears it.
        assert_eq!(runner.phase(), ConsensusPhase::Accepted);
        *runner
            .adaptor
            .pending_accept
            .lock()
            .expect("pending accept lock") = Some(failed_candidate_work(Arc::clone(&parent)));

        let work = failed_candidate_work(Arc::clone(&parent));
        assert!(runner.restart_after_failed_candidate_build(NetClockTimePoint::new(1_020), &work,));

        let after = root
            .closed_ledger()
            .expect("failed candidate must not install a child");
        assert_eq!(after.header().hash, before.header().hash);
        assert_eq!(after.header().seq, 10);
        assert_eq!(runner.prev_ledger_id(), parent_hash);
        assert_eq!(runner.phase(), ConsensusPhase::Open);
        assert!(
            runner
                .adaptor
                .pending_accept
                .lock()
                .expect("pending accept lock")
                .is_none(),
            "failed candidate must not leave accept work scheduled"
        );
    }

    #[test]
    fn stable_recovery_anchor_vetoes_captured_accept_before_child_install() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let parent = Arc::new(Ledger::from_ledger_seq_and_close_time(10, 1_000, false));
        let parent_hash = *parent.header().hash.as_uint256();
        root.on_closed_ledger(Arc::clone(&parent));
        let (_store_dir, inbound) = install_empty_test_coordinator(&mut root);
        let recovery = Uint256::from_u64(0xA11CE);
        assert_ne!(recovery, parent_hash);
        assert!(inbound.coordinator_validation_recovery_target(Some((recovery, 20))));
        assert_eq!(
            inbound.coordinator_validation_recovery_latch().0,
            Some((recovery, 20))
        );

        let mut runner = failed_candidate_test_runner(&mut root);
        assert_eq!(runner.phase(), ConsensusPhase::Accepted);
        runner.execute_accept(
            NetClockTimePoint::new(1_020),
            failed_candidate_work(Arc::clone(&parent)),
        );

        let closed = root.closed_ledger().expect("parent remains installed");
        assert_eq!(*closed.header().hash.as_uint256(), parent_hash);
        assert_eq!(closed.header().seq, 10, "no stale child may be installed");
        assert_eq!(runner.prev_ledger_id(), parent_hash);
        assert_eq!(runner.phase(), ConsensusPhase::Accepted);
        assert_eq!(
            root.status_rpc_state().current_ledger_index(),
            None,
            "accept veto runs before open-ledger/status mutation"
        );
    }

    #[test]
    fn round_validation_eligibility_matches_rippled_pre_start_round() {
        use super::AppRclConsensusAdaptor;

        // keys && seq >= maxDisallowed && !blocked is the baseline.
        assert!(AppRclConsensusAdaptor::round_validation_eligible(
            true, 100, 100, false, false, 0, None, 1_000,
        ));
        assert!(!AppRclConsensusAdaptor::round_validation_eligible(
            false, 100, 100, false, false, 0, None, 1_000,
        ));
        assert!(!AppRclConsensusAdaptor::round_validation_eligible(
            true, 99, 100, false, false, 0, None, 1_000,
        ));
        assert!(!AppRclConsensusAdaptor::round_validation_eligible(
            true, 100, 100, true, false, 0, None, 1_000,
        ));

        // A configured non-standalone UNL must not be expired. Equality is
        // valid, matching rippled's `expires < now` rejection.
        assert!(AppRclConsensusAdaptor::round_validation_eligible(
            true,
            100,
            100,
            false,
            false,
            1,
            Some(1_000),
            1_000,
        ));
        assert!(!AppRclConsensusAdaptor::round_validation_eligible(
            true,
            100,
            100,
            false,
            false,
            1,
            Some(999),
            1_000,
        ));
        assert!(!AppRclConsensusAdaptor::round_validation_eligible(
            true, 100, 100, false, false, 1, None, 1_000,
        ));
        // Standalone skips expiry enforcement, exactly as rippled does.
        assert!(AppRclConsensusAdaptor::round_validation_eligible(
            true, 100, 100, false, true, 1, None, 1_000,
        ));
    }

    #[test]
    fn provisional_inbound_candidate_drives_actual_acquire_ledger_without_adoption() {
        use consensus::algorithm::ConsensusAdaptor as _;

        let mut root = ApplicationRoot::new(0).expect("root should build");
        // A resolver-visible provisional candidate must carry a real header hash
        // and a populated state map: the registry rejects zero-hash acquisition
        // and `LedgerHistory::insert` drops ledgers with an empty state tree.
        let candidate = resolvable_immutable_ledger(10, 0x10);
        let target = *candidate.header().hash.as_uint256();
        let (_store_dir, inbound) =
            install_real_provisional_inbound_candidate(&mut root, Arc::clone(&candidate));
        let stale_set = Uint256::from_u64(0xA11CE);
        {
            let mut transactions = root
                .inbound_transactions()
                .lock()
                .expect("inbound transactions mutex");
            assert!(transactions.get_set(stale_set, true).is_none());
            assert!(transactions.acquire(stale_set).is_some());
        }

        let mut runner = failed_candidate_test_runner(&mut root);
        assert!(runner.adaptor.acquire_ledger(&target).is_none());

        assert!(inbound.is_provisional(&target));
        assert!(inbound.contains(&target));
        assert_eq!(
            *runner
                .adaptor
                .acquiring_ledger
                .lock()
                .expect("acquiring ledger mutex"),
            Some(target),
            "provisional WrongLedger recovery must retain the exact target"
        );
        assert!(
            root.inbound_transactions()
                .lock()
                .expect("inbound transactions mutex")
                .acquire(stale_set)
                .is_some(),
            "a provisional resolver hit must not reset TxQ/inbound transaction round state"
        );
        assert!(root.closed_ledger().is_none());
        assert!(root.published_ledger().is_none());
        assert!(
            inbound
                .acquire(target, candidate.header().seq, AcquireReason::Consensus)
                .is_some(),
            "the exact target remains recoverable until its durable completion"
        );
        inbound.stop();
    }

    #[test]
    fn resolved_consensus_ledger_prunes_stale_inbound_transaction_round() {
        let root = ApplicationRoot::new(0).expect("root should build");
        let inbound = root.inbound_transactions().clone();
        let stale_set = Uint256::from_u64(0xA11CE);

        {
            let mut guard = inbound.lock().expect("inbound transactions mutex");
            assert!(guard.get_set(stale_set, true).is_none());
            assert!(guard.acquire(stale_set).is_some());
        }

        // Sequence 10 retains only sets from [7, 13]. The stale acquisition
        // was created in the initial round (0), so rippled's acquireLedger
        // newRound handoff must retire it before proposal playback.
        reset_inbound_transactions_for_resolved_consensus_ledger(&inbound, 10);

        let mut guard = inbound.lock().expect("inbound transactions mutex");
        assert!(guard.acquire(stale_set).is_none());
        assert!(guard.get_set(Uint256::zero(), false).is_some());
    }

    #[test]
    fn disputed_relay_replaces_hostile_inbound_metadata_with_local_new_envelope() {
        let hostile = TransactionRelayMetadata::new(2, Some(1), Some(true));
        let message = disputed_relay_envelope(vec![0xD0, 0x0D], 9_999);

        assert_eq!(message.status, 1, "disputed relay must emit tsNEW");
        assert_eq!(message.receive_timestamp, Some(9_999));
        assert_eq!(message.deferred, None);
        assert_ne!(message.status, hostile.status);
        assert_ne!(message.receive_timestamp, hostile.receive_timestamp);
        assert_ne!(message.deferred, hostile.deferred);
    }

    #[test]
    fn consensus_pseudo_transaction_voting_requires_proposing_or_standalone_and_quorum() {
        assert!(pseudo_transaction_voting_enabled(
            AppRclConsensusOptions::default(),
            ConsensusMode::Proposing,
        ));
        assert!(!pseudo_transaction_voting_enabled(
            AppRclConsensusOptions::default(),
            ConsensusMode::Observing,
        ));
        assert!(pseudo_transaction_voting_enabled(
            AppRclConsensusOptions {
                standalone: true,
                ..Default::default()
            },
            ConsensusMode::WrongLedger,
        ));
        assert!(trusted_validation_quorum_reached(3, 3));
        assert!(!trusted_validation_quorum_reached(2, 3));
    }

    #[test]
    fn coordinator_reports_rippled_zero_position_mode_demotion() {
        assert!(coordinator_should_report_no_consensus_positions(0, 0));
        assert!(coordinator_should_report_no_consensus_positions(0, 1));
        assert!(!coordinator_should_report_no_consensus_positions(1, 1));
    }

    #[test]
    fn consensus_accept_with_no_positions_downgrades_full_operating_mode() {
        let state = Arc::new(SharedNetworkOpsState::new(NetworkOpsOperatingMode::Full));
        let owner = AppNetworkOpsModeOwner::new(Arc::clone(&state), Arc::new(|| Duration::ZERO));

        update_operating_mode_after_accept(&owner, 0);

        assert_eq!(
            state.operating_mode(),
            NetworkOpsOperatingMode::Syncing,
            "the legacy fallback must pass through rippled's validated-age normalization"
        );

        state.set_operating_mode(NetworkOpsOperatingMode::Full);
        state.set_need_network_ledger(true);
        update_operating_mode_after_accept(&owner, 0);
        assert_eq!(
            state.operating_mode(),
            NetworkOpsOperatingMode::Full,
            "rippled isFull excludes a node waiting for a network ledger"
        );
    }

    #[test]
    fn consensus_decode_discards_malformed_entries_and_keeps_valid_transactions() {
        let source = AccountID::from_hex("1111111111111111111111111111111111111111")
            .expect("source account");
        let destination = AccountID::from_hex("2222222222222222222222222222222222222222")
            .expect("destination account");
        let valid = STTx::new(TxType::PAYMENT, |tx| {
            tx.set_account_id(get_field_by_symbol("sfAccount"), source);
            tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
            tx.set_field_amount(
                get_field_by_symbol("sfAmount"),
                STAmount::new_native(1_000_000, false),
            );
            tx.set_field_amount(
                get_field_by_symbol("sfFee"),
                STAmount::new_native(10, false),
            );
            tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        });
        let valid_bytes = valid.get_serializer().data().to_vec();
        let malformed_bytes = [0; protocol::TX_MIN_SIZE_BYTES - 1];

        let (transactions, malformed) = decode_consensus_accept_transactions(
            Uint256::zero(),
            [
                (valid_bytes.len(), valid_bytes.as_slice()),
                (malformed_bytes.len(), &malformed_bytes),
            ],
        );

        assert_eq!(transactions.len(), 1);
        assert_eq!(
            transactions[0].get_transaction_id(),
            valid.get_transaction_id()
        );
        assert_eq!(malformed.len(), 1);
        assert_eq!(malformed[0].0, malformed_bytes.len());
    }
}

impl ConsensusRunner for AppConsensus {
    fn peer_proposal(&mut self, now: NetClockTimePoint, peer_pos: &RclCxPeerPos) -> bool {
        // Match NetworkOPsImp::processTrustedProposal: a proposal signed by
        // either of this node's validation keys must neither influence local
        // consensus nor be relayed. It may be a duplicate route or an
        // operator key-reuse error, but it is not a peer position.
        if self
            .adaptor
            .validator_keys
            .keys
            .as_ref()
            .is_some_and(|keys| {
                keys.public_key == *peer_pos.public_key()
                    || keys.master_public_key == *peer_pos.public_key()
            })
        {
            tracing::error!(
                target: "consensus",
                "received a trusted proposal signed by this node's validator key"
            );
            return false;
        }

        // Signature was verified by `overlay_impl.rs::on_propose_ledger` before
        // this proposal was queued — matching rippled's `checkPropose` which
        // calls `peerPos.checkSign()` and drops invalid proposals before they
        // reach `processTrustedProposal` / `peer_proposal`.
        let our_prev = *self.state.prev_ledger_id();
        let their_prev = *peer_pos.proposal().prev_ledger();
        let accepted = self.state.peer_proposal(&self.adaptor, now, peer_pos);
        self.publish_consensus_mode();
        if !accepted && our_prev != their_prev {
            let local_lcl = self
                .adaptor
                .app_root
                .closed_ledger()
                .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
            let validated_anchor = self
                .adaptor
                .app_root
                .validated_ledger()
                .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
            tracing::debug!(
                target: "lcl_audit",
                our_prev = %our_prev,
                their_prev = %their_prev,
                phase = ?self.state.phase(),
                ?local_lcl,
                ?validated_anchor,
                need_network_ledger = self.adaptor.app_root.need_network_ledger(),
                "LCL_AUDIT peer proposal rejected for previous-ledger mismatch"
            );
        }
        accepted
    }

    fn timer_tick(&mut self, now: NetClockTimePoint) -> Option<PendingAcceptWork> {
        self.state.timer_entry(&self.adaptor, now);
        self.publish_consensus_mode();
        // If on_accept fired during timer_entry, pending_accept will be Some.
        self.adaptor
            .pending_accept
            .lock()
            .expect("pending_accept mutex must not be poisoned")
            .take()
    }

    fn start_round(
        &mut self,
        now: NetClockTimePoint,
        prev_ledger_id: Uint256,
        prev_ledger: RclCxLedger,
        proposing: bool,
    ) {
        // Match NetworkOPsImp::beginConsensus: trust state is derived from
        // the locally available prevLedger (the parent of the current open
        // ledger), not from networkClosed. The generic consensus engine is
        // explicitly designed for `prev_ledger_id` to name an unavailable
        // preferred target and will enter WrongLedger/GetConsL1 as needed.
        let lcl = prev_ledger.ledger();
        if let Err(error) = self
            .adaptor
            .app_root
            .refresh_validator_trust_for_consensus(lcl.as_ref())
        {
            // rippled lets MissingNode propagate out of Ledger::negativeUNL.
            // Preserve the prior exclusion set and do not start a round with
            // quorum inputs that could not be read from the parent ledger.
            tracing::error!(
                target: "consensus",
                ledger_hash = %lcl.header().hash,
                ledger_seq = lcl.header().seq,
                ?error,
                "consensus round not started: failed to read parent ledger NegativeUNL"
            );
            return;
        }

        if self.adaptor.validators.count() > 0 && self.adaptor.validators.unl_size() == 0 {
            self.adaptor.network_ops_mode_owner.set_unl_blocked(true);
        } else {
            self.adaptor.network_ops_mode_owner.set_unl_blocked(false);
        }
        let validating = self.adaptor.update_validating_for_round(&prev_ledger);
        // A Full node may still have a locally usable parent while a strict
        // validation-backed recovery tree for a different network ledger is
        // being acquired. rippled's acquisition normally resolves this
        // transient quickly; Quaxar's externalized tree build can span many
        // rounds. Observe during that interval instead of proposing on a
        // known stale local fork. Normal proposing resumes after exact durable
        // recovery clears the latch or when the latch already names this
        // round's concrete parent.
        let local_parent_hash = *lcl.header().hash.as_uint256();
        let validation_recovery = self
            .adaptor
            .coordinator_inbound()
            .and_then(|inbound| inbound.coordinator_validation_recovery_latch().0);
        let conflicting_validation_recovery =
            validation_recovery_conflicts_with_parent(validation_recovery, local_parent_hash);
        let actual_proposing = proposing
            && validating
            && !conflicting_validation_recovery
            && self.adaptor.network_ops_mode_owner.operating_mode()
                == crate::network::network_ops::NetworkOpsOperatingMode::Full;
        tracing::debug!(
            target: "lcl_audit",
            requested_prev_ledger = %prev_ledger_id,
            local_parent_hash = %lcl.header().hash,
            local_parent_seq = lcl.header().seq,
            requested_proposing = proposing,
            actual_proposing,
            conflicting_validation_recovery,
            is_validator = self.adaptor.is_validator(),
            validating,
            standalone = self.adaptor.options.standalone,
            operating_mode = ?self.adaptor.network_ops_mode_owner.operating_mode(),
            need_network_ledger = self.adaptor.app_root.need_network_ledger(),
            "LCL_AUDIT consensus round start"
        );
        let (now_untrusted, now_trusted) = self.compute_trust_changes();
        if !now_trusted.is_empty() {
            if let Some(negative_unl_vote) = self.adaptor.negative_unl_vote.as_ref() {
                let node_ids = now_trusted
                    .iter()
                    .map(protocol::calc_node_id)
                    .collect::<StdHashSet<_>>();
                negative_unl_vote.new_validators(lcl.header().seq.saturating_add(1), &node_ids);
            }
        }
        self.state.start_round(
            &self.adaptor,
            now,
            prev_ledger_id,
            prev_ledger,
            &now_untrusted,
            actual_proposing,
        );
        self.publish_consensus_mode();
    }

    fn got_tx_set(&mut self, now: NetClockTimePoint, tx_set: consensus::RclTxSet) {
        self.state.got_tx_set(&self.adaptor, now, &tx_set);
        self.publish_consensus_mode();
    }

    fn execute_accept(&mut self, now: NetClockTimePoint, work: PendingAcceptWork) {
        self.do_accept_and_start_next_round(now, work);
        self.publish_consensus_mode();
    }

    fn phase(&self) -> consensus::algorithm::ConsensusPhase {
        self.state.phase()
    }

    fn prev_ledger_id(&self) -> Uint256 {
        *self.state.prev_ledger_id()
    }
}

#[cfg(test)]
mod sync_tree_conversion_tests {
    use super::{
        open_ledger_consensus_snapshot, resolved_consensus_ledger_is_adoptable,
        should_acquire_consensus_ledger, sync_tree_to_rcl_tx_set,
    };
    use basics::hardened_hash::HardenedHashBuilder;
    use basics::tagged_cache::MonotonicClock;
    use protocol::{STAmount, STTx, TxType, get_field_by_symbol, serialize_blob};
    use shamap::item::SHAMapItem;
    use shamap::storage::StorageTree;
    use shamap::sync::{SHAMapType, SyncState, SyncTree};
    use shamap::tree_node::SHAMapNodeType;
    use std::sync::Arc;

    fn cache() -> consensus::rcl::RclTxSetSharedCache {
        Arc::new(shamap::tree_node_cache::TreeNodeCache::new(
            "sync-tree-conversion-test",
            32,
            time::Duration::minutes(5),
            basics::tagged_cache::MonotonicClock::default(),
        ))
    }

    fn payment(fill: u8) -> STTx {
        STTx::new(TxType::PAYMENT, |tx| {
            tx.set_field_u32(get_field_by_symbol("sfSequence"), u32::from(fill));
            tx.set_field_amount(
                get_field_by_symbol("sfAmount"),
                STAmount::new_native(u64::from(fill), false),
            );
            tx.set_field_amount(
                get_field_by_symbol("sfFee"),
                STAmount::new_native(10, false),
            );
        })
    }

    fn completed_sync_tree(txs: &[STTx], cache: consensus::rcl::RclTxSetSharedCache) -> SyncTree {
        let cache: Arc<
            shamap::tree_node_cache::TreeNodeCache<MonotonicClock, HardenedHashBuilder>,
        > = cache;
        let mut map = StorageTree::new(1, false, 1, cache);
        for tx in txs {
            let item = SHAMapItem::new(tx.get_transaction_id(), serialize_blob(tx));
            map.add_item(SHAMapNodeType::TransactionNm, item)
                .expect("insert into a fresh test tree should not need fetches");
        }
        map.unshare();

        let tree = SyncTree::from_root_with_type(
            map.root(),
            SHAMapType::Transaction,
            false,
            1,
            SyncState::Modifying,
        );
        tree.set_full();
        tree
    }

    #[test]
    fn provisional_resolver_ledger_is_not_adoptable_by_wrong_ledger_recovery() {
        assert!(resolved_consensus_ledger_is_adoptable(false));
        assert!(
            !resolved_consensus_ledger_is_adoptable(true),
            "a provisional identity must not reset TxQ or start a generic replacement round"
        );
    }

    #[test]
    fn consensus_ledger_acquisition_is_coalesced_by_hash() {
        let first = basics::base_uint::Uint256::from_u64(1);
        let second = basics::base_uint::Uint256::from_u64(2);
        let mut acquiring = None;

        assert!(should_acquire_consensus_ledger(&mut acquiring, first));
        assert!(!should_acquire_consensus_ledger(&mut acquiring, first));
        assert!(should_acquire_consensus_ledger(&mut acquiring, second));
        assert!(!should_acquire_consensus_ledger(&mut acquiring, second));
    }

    #[test]
    fn sync_tree_to_rcl_tx_set_preserves_id_and_membership() {
        let tx1 = payment(1);
        let tx2 = payment(2);
        let tx1_id = tx1.get_transaction_id();
        let tx2_id = tx2.get_transaction_id();

        let shared_cache = cache();
        let tree = completed_sync_tree(&[tx1, tx2], cache());
        let adopted = sync_tree_to_rcl_tx_set(&tree, &shared_cache);

        assert!(adopted.exists(tx1_id));
        assert!(adopted.exists(tx2_id));
        assert_eq!(adopted.id(), *tree.root().get_hash().as_uint256());
    }

    #[test]
    fn consensus_snapshot_preserves_outer_and_batch_inner_transaction_ids() {
        let outer = Arc::new(payment(1));
        let first_inner = Arc::new(payment(2));
        let second_inner = Arc::new(payment(3));
        let transactions = vec![
            Arc::clone(&outer),
            Arc::clone(&first_inner),
            Arc::clone(&second_inner),
        ];

        let set = open_ledger_consensus_snapshot(cache(), 11, &transactions);

        assert!(set.exists(outer.get_transaction_id()));
        assert!(set.exists(first_inner.get_transaction_id()));
        assert!(set.exists(second_inner.get_transaction_id()));
        assert_eq!(set.all_items().len(), 3);
    }

    #[test]
    fn sync_tree_to_rcl_tx_set_matches_hash_of_independently_built_equivalent_set() {
        let tx1 = payment(3);
        let tx2 = payment(4);

        let tree = completed_sync_tree(&[tx1.clone(), tx2.clone()], cache());
        let adopted = sync_tree_to_rcl_tx_set(&tree, &cache());

        let mut rebuilt = consensus::RclTxSet::new(cache(), 1);
        {
            let mut editable = rebuilt.mutable_view();
            editable.insert(&consensus::RclCxTxRef::from_transaction(&tx1));
            editable.insert(&consensus::RclCxTxRef::from_transaction(&tx2));
            rebuilt = editable.freeze();
        }

        assert_eq!(adopted.id(), rebuilt.id());
    }
}
