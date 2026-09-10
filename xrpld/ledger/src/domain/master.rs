//! Owner-level `LedgerMaster` composition above the landed Rust ledger slices.
//!
//! This ports the ledger-owned state and gating that do not need the wider
//! application graph:
//! - validated / published / closed ledger holders,
//! - complete-ledger tracking and cache clearing,
//! - validated-range and transaction-id lookup for cached ledgers,
//! - published / validated ledger age calculations,
//! - fetch-pack cache ownership and single-dispatch gating,
//! - and the pathfinding work-dispatch counters.

use crate::{
    CanonicalTXSet, FetchPackCache, Ledger, LedgerConfig, LedgerHistory, LedgerHolder,
    LedgerJournal, LedgerMasterSweepTarget, LedgerPersistence, LocalTxs, NullLedgerJournal,
    ReadView, SHAMapHash, sweep_ledger_master_like,
};
use basics::base_uint::Uint256;
use basics::hardened_hash::HardenedHashBuilder;
use basics::range_set::prev_missing;
use basics::range_set::{RangeSet, range};
use basics::tagged_cache::{CacheClock, MonotonicClock};
use protocol::STTx;
use shamap::family::{FullBelowCache, MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use shamap::traversal::TraversalError;
use std::hash::BuildHasher;
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use time::Duration;

pub const LEDGER_MASTER_DEFAULT_HISTORY_AGE: Duration = Duration::minutes(5);
pub const LEDGER_MASTER_DEFAULT_FETCH_PACK_AGE: Duration = Duration::seconds(45);
pub const LEDGER_MASTER_DEFAULT_PATH_FIND_JOB_LIMIT: u32 = 2;
pub const LEDGER_MASTER_MAX_PUBLISH_GAP: u32 = 100;

/// Rippled's `populateFetchPack` limits. State-map differences are allowed to
/// be larger than the reply continuation threshold; transaction maps are
/// independently bounded because a requester is unlikely to have historical
/// transaction nodes.
pub const FETCH_PACK_STATE_NODE_LIMIT: usize = 16_384;
pub const FETCH_PACK_TRANSACTION_NODE_LIMIT: usize = 512;
pub const FETCH_PACK_REPLY_CONTINUATION_LIMIT: usize = 512;

/// One object in a ledger-owned fetch pack. The overlay crate converts these
/// into `TMIndexedObject` so ledger assembly stays independent of transport.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FetchPackObject {
    pub hash: Uint256,
    pub data: Vec<u8>,
    pub ledger_seq: u32,
}

/// The request failures for which PeerImp charges a requester. A missing
/// immediate predecessor is distinct from a later history-chain stop: no
/// object can be sent for the initial requested predecessor, so rippled
/// charges `kFeeRequestNoReply`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FetchPackBuildError {
    Stale,
    RequestedLedgerMissing,
    RequestedLedgerPredecessorMissing,
    RequestedLedgerOpen,
    RequestedLedgerTooEarly,
    Traversal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LedgerMasterConfig {
    pub history_cache_size: usize,
    pub history_cache_age: Duration,
    pub fetch_pack_cache_size: usize,
    pub fetch_pack_cache_age: Duration,
    pub path_find_job_limit: u32,
}

impl Default for LedgerMasterConfig {
    fn default() -> Self {
        Self {
            history_cache_size: 256,
            history_cache_age: LEDGER_MASTER_DEFAULT_HISTORY_AGE,
            fetch_pack_cache_size: 65_536,
            fetch_pack_cache_age: LEDGER_MASTER_DEFAULT_FETCH_PACK_AGE,
            path_find_job_limit: LEDGER_MASTER_DEFAULT_PATH_FIND_JOB_LIMIT,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LedgerMasterCaughtUp {
    Yes,
    No { reason: &'static str },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LedgerMasterPathWork {
    NewRequest,
    OrderBookDb,
}

/// Exact result of comparing one candidate ledger to one compatibility anchor.
/// Kept structured so recovery logs can identify the failing anchor instead of
/// emitting only the final `is_compatible` boolean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LedgerCompatibilityAnchorAudit {
    pub hash: Uint256,
    pub seq: u32,
    pub candidate_ancestor: Option<Uint256>,
    pub matches: bool,
}

/// Compatibility evidence for a candidate considered by preferred-LCL recovery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LedgerCompatibilityAudit {
    pub candidate_hash: Uint256,
    pub candidate_seq: u32,
    pub candidate_parent_hash: Uint256,
    pub validated_anchor: Option<LedgerCompatibilityAnchorAudit>,
    pub last_valid_anchor: Option<LedgerCompatibilityAnchorAudit>,
}

impl LedgerCompatibilityAudit {
    pub fn compatible(&self) -> bool {
        self.validated_anchor.is_none_or(|anchor| anchor.matches)
            && self.last_valid_anchor.is_none_or(|anchor| anchor.matches)
    }
}

#[derive(Debug, Default)]
struct PathState {
    path_ledger: Option<Arc<Ledger>>,
    path_find_threads: u32,
    new_request: bool,
}

#[derive(Debug)]
pub struct LedgerMaster<C = MonotonicClock, S = HardenedHashBuilder> {
    config: LedgerMasterConfig,
    closed_ledger: LedgerHolder,
    valid_ledger: LedgerHolder,
    published_ledger: LedgerHolder,
    ledger_history: LedgerHistory<C, S>,
    fetch_packs: Arc<FetchPackCache<C, S>>,
    local_txs: LocalTxs,
    held_transactions: Mutex<CanonicalTXSet>,
    complete_ledgers: Mutex<RangeSet<u32>>,
    path_state: Mutex<PathState>,
    got_fetch_pack_in_flight: AtomicBool,
    pub_ledger_close: AtomicU32,
    valid_ledger_sign: AtomicU32,
    valid_ledger_seq: AtomicU32,
    /// Highest quorum-backed ledger observed by `checkAccept(hash, seq)`.
    /// This is intentionally retained even while the ledger is being
    /// acquired, matching rippled's `lastValidLedger_` safety anchor.
    last_valid_ledger: Mutex<Option<(Uint256, u32)>>,
}

impl<C> LedgerMaster<C, HardenedHashBuilder>
where
    C: CacheClock + Clone,
{
    pub fn new(clock: C, config: LedgerMasterConfig) -> Self {
        Self::with_hasher(clock, HardenedHashBuilder::default(), config)
    }
}

impl<C, S> LedgerMaster<C, S>
where
    C: CacheClock + Clone,
    S: BuildHasher + Clone,
{
    pub fn with_hasher(clock: C, hasher: S, config: LedgerMasterConfig) -> Self {
        Self::with_parts(
            LedgerHistory::with_hasher(
                config.history_cache_size,
                config.history_cache_age,
                clock.clone(),
                hasher.clone(),
            ),
            FetchPackCache::with_hasher(
                config.fetch_pack_cache_size,
                config.fetch_pack_cache_age,
                clock,
                hasher,
            ),
            LocalTxs::new(),
            config,
        )
    }

    pub fn with_parts(
        ledger_history: LedgerHistory<C, S>,
        fetch_packs: FetchPackCache<C, S>,
        local_txs: LocalTxs,
        config: LedgerMasterConfig,
    ) -> Self {
        Self {
            config,
            closed_ledger: LedgerHolder::new(),
            valid_ledger: LedgerHolder::new(),
            published_ledger: LedgerHolder::new(),
            ledger_history,
            fetch_packs: Arc::new(fetch_packs),
            local_txs,
            held_transactions: Mutex::new(CanonicalTXSet::new(Uint256::zero())),
            complete_ledgers: Mutex::new(RangeSet::new()),
            path_state: Mutex::new(PathState::default()),
            got_fetch_pack_in_flight: AtomicBool::new(false),
            pub_ledger_close: AtomicU32::new(0),
            valid_ledger_sign: AtomicU32::new(0),
            valid_ledger_seq: AtomicU32::new(0),
            last_valid_ledger: Mutex::new(None),
        }
    }

    pub fn config(&self) -> LedgerMasterConfig {
        self.config
    }

    pub fn ledger_history(&self) -> &LedgerHistory<C, S> {
        &self.ledger_history
    }

    pub fn fetch_pack_cache(&self) -> &FetchPackCache<C, S> {
        &self.fetch_packs
    }

    /// Shared LedgerMaster fetch-pack owner used by inbound acquisition
    /// filters. rippled has one 65,536-entry cache, not a second registry-local
    /// copy with a different lifetime.
    pub fn fetch_pack_cache_arc(&self) -> Arc<FetchPackCache<C, S>> {
        Arc::clone(&self.fetch_packs)
    }

    pub fn local_txs(&self) -> &LocalTxs {
        &self.local_txs
    }

    pub fn add_held_transaction(&self, transaction: Arc<STTx>) {
        self.held_transactions
            .lock()
            .expect("held-transactions mutex must not be poisoned")
            .insert(transaction);
    }

    pub fn held_transaction_count(&self) -> usize {
        self.held_transactions
            .lock()
            .expect("held-transactions mutex must not be poisoned")
            .len()
    }

    pub fn pop_acct_transaction(&self, tx: &Arc<STTx>) -> Option<Arc<STTx>> {
        self.held_transactions
            .lock()
            .expect("held-transactions mutex must not be poisoned")
            .pop_acct_transaction(tx)
    }

    pub fn take_held_transactions(&self, next_ledger_hash: Uint256) -> CanonicalTXSet {
        let mut held_transactions = self
            .held_transactions
            .lock()
            .expect("held-transactions mutex must not be poisoned");
        let mut set = CanonicalTXSet::new(next_ledger_hash);
        std::mem::swap(&mut *held_transactions, &mut set);
        set
    }

    pub fn apply_held_transactions<F>(&self, next_ledger_hash: Uint256, mut process: F) -> usize
    where
        F: FnMut(CanonicalTXSet),
    {
        let set = self.take_held_transactions(next_ledger_hash);
        let count = set.len();
        if !set.is_empty() {
            process(set);
        }
        count
    }

    pub fn set_closed_ledger(&self, ledger: Arc<Ledger>) {
        self.closed_ledger.set(Some(ledger));
    }

    pub fn closed_ledger(&self) -> Option<Arc<Ledger>> {
        self.closed_ledger.get()
    }

    pub fn validated_ledger(&self) -> Option<Arc<Ledger>> {
        self.valid_ledger.get()
    }

    pub fn published_ledger(&self) -> Option<Arc<Ledger>> {
        self.published_ledger.get()
    }

    pub fn get_ledger_by_hash(&self, hash: SHAMapHash) -> Option<Arc<Ledger>> {
        if let Some(ledger) = self.ledger_history.get_cached_ledger_by_hash(hash) {
            return Some(ledger);
        }

        let ledger = self.closed_ledger.get();
        if ledger
            .as_ref()
            .is_some_and(|ledger| ledger.header().hash == hash)
        {
            return ledger;
        }

        None
    }

    pub fn get_ledger_by_seq<J: LedgerJournal>(
        &self,
        seq: u32,
        journal: &J,
    ) -> Option<Arc<Ledger>> {
        if seq <= self.valid_ledger_seq()
            && let Some(valid) = self.valid_ledger.get()
        {
            if valid.header().seq == seq {
                return Some(valid);
            }

            if let Some(hash) = valid.hash_of_seq(seq, journal)
                && let Some(ledger) = self.ledger_history.get_cached_ledger_by_hash(hash)
            {
                return Some(ledger);
            }
        }

        if let Some(ledger) = self.ledger_history.get_cached_ledger_by_seq(seq) {
            tracing::debug!(target: "ledger", seq, "Ledger fetched from history");
            return Some(ledger);
        }

        let ledger = self.closed_ledger.get();
        if ledger
            .as_ref()
            .is_some_and(|ledger| ledger.header().seq == seq)
        {
            return ledger;
        }

        self.clear_ledger(seq);
        None
    }

    pub fn valid_ledger_seq(&self) -> u32 {
        self.valid_ledger_seq.load(Ordering::SeqCst)
    }

    pub fn have_validated(&self) -> bool {
        !self.valid_ledger.empty()
    }

    /// Record the highest sequence for which trusted validations reached
    /// quorum. This must happen before acquisition: an unavailable but
    /// quorum-backed ledger is still the compatibility anchor for later LCL
    /// switches.
    pub fn note_last_valid_ledger(&self, hash: Uint256, seq: u32) {
        if seq == 0 {
            return;
        }
        let mut last = self
            .last_valid_ledger
            .lock()
            .expect("last-valid-ledger mutex must not be poisoned");
        if last.is_none_or(|(_, last_seq)| seq > last_seq) {
            *last = Some((hash, seq));
        }
    }

    pub fn last_valid_ledger(&self) -> Option<(Uint256, u32)> {
        *self
            .last_valid_ledger
            .lock()
            .expect("last-valid-ledger mutex must not be poisoned")
    }

    fn compatibility_anchor_audit(
        ledger: &Ledger,
        hash: Uint256,
        seq: u32,
    ) -> LedgerCompatibilityAnchorAudit {
        // Matches rippled's areCompatible (View.cpp:134-192):
        // When validLedger.seq > testLedger.seq, rippled calls
        //   hashOfSeq(validLedger, testLedger.seq)
        // i.e. it looks DOWN from the HIGHER ledger to check ancestry.
        // We only have the candidate (lower) ledger here, so:
        // - candidate.seq < anchor.seq: can't look up, treat as compatible
        //   (rippled: "if (hash && ..." — only fails on positive mismatch)
        // - candidate.seq == anchor.seq: compare hashes directly
        // - candidate.seq > anchor.seq: look down via skip-list
        let (candidate_ancestor, matches) = if ledger.header().seq < seq {
            // Cannot verify from candidate's perspective — the anchor is AHEAD.
            // Rippled would ask the anchor to look down, and if it can't resolve
            // (hashOfSeq returns nullopt), it returns compatible (true).
            // We don't have the anchor ledger object here, so we cannot disprove
            // compatibility. Match rippled: assume compatible.
            (None, true)
        } else if ledger.header().seq == seq {
            let ancestor = Some(*ledger.header().hash.as_uint256());
            (ancestor, ancestor == Some(hash))
        } else if ledger.header().seq == seq.saturating_add(1) {
            let ancestor = Some(*ledger.header().parent_hash.as_uint256());
            (ancestor, ancestor == Some(hash))
        } else {
            let ancestor = ledger
                .hash_of_seq(seq, &NullLedgerJournal)
                .map(|a| *a.as_uint256());
            // Rippled: only incompatible if hash IS resolved AND doesn't match.
            // If hash_of_seq returns None (skip-list gap), assume compatible.
            let m = match ancestor {
                Some(a) => a == hash,
                None => true, // can't disprove → compatible
            };
            (ancestor, m)
        };
        LedgerCompatibilityAnchorAudit {
            hash,
            seq,
            candidate_ancestor,
            matches,
        }
    }

    /// Return the exact validated and quorum-anchor comparisons that determine
    /// whether a preferred-LCL candidate may replace the local closed ledger.
    pub fn compatibility_audit(&self, ledger: &Ledger) -> LedgerCompatibilityAudit {
        let validated_anchor = self.validated_ledger().map(|validated| {
            Self::compatibility_anchor_audit(
                ledger,
                *validated.header().hash.as_uint256(),
                validated.header().seq,
            )
        });
        let last_valid_anchor = self
            .last_valid_ledger()
            .map(|(hash, seq)| Self::compatibility_anchor_audit(ledger, hash, seq));
        LedgerCompatibilityAudit {
            candidate_hash: *ledger.header().hash.as_uint256(),
            candidate_seq: ledger.header().seq,
            candidate_parent_hash: *ledger.header().parent_hash.as_uint256(),
            validated_anchor,
            last_valid_anchor,
        }
    }

    /// Equivalent to LedgerMaster::isCompatible. A candidate must remain on
    /// both the validated chain and the highest quorum-backed chain observed
    /// before acquisition.
    pub fn is_compatible(&self, ledger: &Ledger) -> bool {
        self.compatibility_audit(ledger).compatible()
    }

    /// too far from network close time, or too far ahead of the valid ledger.
    pub fn can_be_current(&self, ledger: &Ledger, now_close_time: u32) -> bool {
        if let Some(valid_ledger) = self.validated_ledger()
            && ledger.header().seq < valid_ledger.header().seq
        {
            return false;
        }

        let parent_close_time = ledger.header().parent_close_time;
        // Use a larger limit when the validated ledger itself is old (we're catching up).
        // bypasses can_be_current entirely — so this only applies to no-quorum cases.
        let age_limit = Duration::minutes(5);
        if (self.have_validated() || ledger.header().seq > 10)
            && close_time_distance(now_close_time, parent_close_time) > age_limit
        {
            return false;
        }

        if let Some(valid_ledger) = self.validated_ledger() {
            let mut max_seq = valid_ledger.header().seq.saturating_add(10);
            if now_close_time > valid_ledger.header().parent_close_time {
                max_seq = max_seq.saturating_add(
                    now_close_time.saturating_sub(valid_ledger.header().parent_close_time) / 2,
                );
            }

            if ledger.header().seq > max_seq {
                return false;
            }
        }

        true
    }

    /// validation quorum, and the current validated sequence before promotion.
    pub fn check_accept_ledger(
        &self,
        ledger: &Ledger,
        validation_count: usize,
        needed_validations: usize,
        now_close_time: u32,
    ) -> bool {
        if !self.can_be_current(ledger, now_close_time) {
            return false;
        }
        if ledger.header().seq <= self.valid_ledger_seq() {
            return false;
        }
        if validation_count < needed_validations {
            return false;
        }
        true
    }

    /// work is needed. Returns true if advancement should be attempted.
    pub fn try_advance(&self) -> bool {
        // Can only advance with at least one validated ledger
        self.have_validated()
    }

    ///
    /// Advances the published ledger to match the validated ledger.
    /// Returns the number of ledgers published.
    pub fn do_advance(&self) -> usize {
        let valid = self.validated_ledger();
        let pub_ledger = self.published_ledger();

        let valid_seq = valid.as_ref().map(|l| l.header().seq).unwrap_or(0);
        let Some(val_ledger) = valid.as_ref() else {
            return 0;
        };

        if pub_ledger.is_none() {
            self.set_pub_ledger(Arc::clone(val_ledger));
            return 1;
        }

        let pub_seq = pub_ledger.as_ref().map(|l| l.header().seq).unwrap_or(0);
        if valid_seq <= pub_seq {
            return 0;
        }

        if valid_seq > pub_seq.saturating_add(LEDGER_MASTER_MAX_PUBLISH_GAP) {
            let gap_start = pub_seq + 1;
            let gap_end = valid_seq;
            tracing::warn!(target: "ledger", gap_start, gap_end, "Ledger gap detected");
            self.set_pub_ledger(Arc::clone(val_ledger));
            return 1;
        }

        let mut published = 0;

        // using hashOfSeq to get intermediate ledger hashes from the
        // validated ledger's skip list.
        for seq in (pub_seq + 1)..=valid_seq {
            if seq == valid_seq {
                // The validated ledger itself
                self.set_pub_ledger(Arc::clone(val_ledger));
                published += 1;
            } else {
                // Look up hash from validated ledger's skip list
                let hash = val_ledger.hash_of_seq(seq, &NullLedgerJournal);
                if let Some(hash) = hash {
                    if !hash.is_zero() {
                        // Check if we have this ledger in history
                        if let Some(ledger) = self.ledger_history.get_cached_ledger_by_hash(hash) {
                            self.set_pub_ledger(Arc::clone(&ledger));
                            published += 1;
                        } else {
                            // Don't have it — stop here, can't skip
                            break;
                        }
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        published
    }

    pub fn set_valid_ledger(
        &self,
        ledger: Arc<Ledger>,
        consensus_hash: Option<Uint256>,
        sign_time: Option<u32>,
    ) -> Result<(), TraversalError> {
        let validated_seq = ledger.header().seq;
        tracing::info!(target: "ledger", validated_seq, "New validated ledger");
        self.valid_ledger.set(Some(Arc::clone(&ledger)));
        self.valid_ledger_sign.store(
            sign_time.unwrap_or(ledger.header().close_time),
            Ordering::SeqCst,
        );
        self.valid_ledger_seq
            .store(ledger.header().seq, Ordering::SeqCst);
        self.local_txs.sweep(ledger.as_ref())?;
        self.ledger_history.insert(Arc::clone(&ledger), true);
        self.ledger_history.validated_ledger(ledger, consensus_hash);
        Ok(())
    }

    /// Like `set_valid_ledger` but skips `local_txs.sweep()`.
    /// Used during catchup when the ledger's state map may not be fully
    /// traversable (only acquired delta nodes are loaded).
    pub fn set_valid_ledger_no_sweep(
        &self,
        ledger: Arc<Ledger>,
        consensus_hash: Option<Uint256>,
        sign_time: Option<u32>,
    ) {
        self.valid_ledger.set(Some(Arc::clone(&ledger)));
        self.valid_ledger_sign.store(
            sign_time.unwrap_or(ledger.header().close_time),
            Ordering::SeqCst,
        );
        self.valid_ledger_seq
            .store(ledger.header().seq, Ordering::SeqCst);
        self.ledger_history.insert(Arc::clone(&ledger), true);
        self.ledger_history.validated_ledger(ledger, consensus_hash);
    }

    pub fn set_pub_ledger(&self, ledger: Arc<Ledger>) {
        let published_seq = ledger.header().seq;
        tracing::info!(target: "ledger", published_seq, "Ledger published");
        self.pub_ledger_close
            .store(ledger.header().close_time, Ordering::SeqCst);
        self.published_ledger.set(Some(ledger));
    }

    pub fn set_full_ledger(
        &self,
        persistence: &LedgerPersistence,
        mut ledger: Arc<Ledger>,
        is_synchronous: bool,
        is_current: bool,
        consensus_hash: Option<Uint256>,
        sign_time: Option<u32>,
    ) -> Result<bool, TraversalError> {
        {
            let ledger = Arc::make_mut(&mut ledger);
            ledger.set_validated();
            ledger.set_full();
        }

        if is_current {
            self.ledger_history.insert(Arc::clone(&ledger), true);
        }

        if ledger.header().seq != 0 {
            let prev_seq = ledger.header().seq - 1;
            if self.have_ledger(prev_seq) {
                let prev_ledger = self.get_ledger_by_seq(prev_seq, &NullLedgerJournal);
                if prev_ledger
                    .as_ref()
                    .is_none_or(|prev| prev.header().hash != ledger.header().parent_hash)
                {
                    self.fix_mismatch(ledger.as_ref());
                }
            }
        }

        // Mark before queue admission so an eager worker's failed-save
        // callback cannot clear the range and then lose a later optimistic
        // insert. Asynchronous failure retracts it through failed_save; a
        // synchronous failure is directly observable below.
        let seq = ledger.header().seq;
        self.mark_ledger_complete(seq);
        let saved =
            persistence.pend_save_validated(Arc::clone(&ledger), is_synchronous, is_current);
        if !saved {
            self.clear_ledger(seq);
        }

        if ledger.header().seq > self.valid_ledger_seq() {
            self.set_valid_ledger(Arc::clone(&ledger), consensus_hash, sign_time)?;
        }

        if self.published_ledger.empty() {
            self.set_pub_ledger(ledger);
        }

        Ok(saved)
    }

    /// Retract only the exact provisional identity. A newer ledger at the
    /// same sequence must keep its history, slots, and complete-range claim.
    pub fn revoke_provisional_ledger(&self, hash: SHAMapHash, seq: u32) {
        let matches =
            |ledger: Arc<Ledger>| ledger.header().hash == hash && ledger.header().seq == seq;
        let cleared_valid =
            self.valid_ledger.get().is_some_and(matches) && self.valid_ledger.clear_if_hash(hash);
        let cleared_published = self.published_ledger.get().is_some_and(matches)
            && self.published_ledger.clear_if_hash(hash);
        let cleared_closed =
            self.closed_ledger.get().is_some_and(matches) && self.closed_ledger.clear_if_hash(hash);
        let removed_history = self.ledger_history.remove_exact(hash, seq);
        // Early resolver visibility is only used for Consensus/Generic
        // acquisitions, neither of which may claim a complete-history range.
        // Do not erase a sequence interval without a matching range owner.
        if !(cleared_valid || cleared_published || cleared_closed || removed_history) {
            return;
        }
        if cleared_valid {
            self.valid_ledger_sign.store(0, Ordering::SeqCst);
            self.valid_ledger_seq.store(0, Ordering::SeqCst);
        }
        if cleared_published {
            self.pub_ledger_close.store(0, Ordering::SeqCst);
        }
        let mut last_valid = self
            .last_valid_ledger
            .lock()
            .expect("last-valid-ledger mutex must not be poisoned");
        if last_valid.is_some_and(|(last_hash, _)| last_hash == *hash.as_uint256()) {
            *last_valid = None;
        }
    }

    pub fn mark_ledger_complete(&self, seq: u32) {
        self.complete_ledgers
            .lock()
            .expect("complete-ledgers mutex must not be poisoned")
            .insert(seq);
    }

    /// Apply one verified contiguous history interval, matching
    /// `LedgerMaster::tryFill`'s `completeLedgers_.insert(range(...))`.
    pub fn mark_ledger_complete_range(&self, min: u32, max: u32) {
        if min > max {
            return;
        }
        self.complete_ledgers
            .lock()
            .expect("complete-ledgers mutex must not be poisoned")
            .insert_interval(range(min, max));
    }

    pub fn have_ledger(&self, seq: u32) -> bool {
        self.complete_ledgers
            .lock()
            .expect("complete-ledgers mutex must not be poisoned")
            .contains(seq)
    }

    pub fn clear_ledger(&self, seq: u32) {
        self.complete_ledgers
            .lock()
            .expect("complete-ledgers mutex must not be poisoned")
            .erase_interval(range(seq, seq));
    }

    pub fn clear_prior_ledgers(&self, seq: u32) {
        if seq == 0 {
            return;
        }

        self.complete_ledgers
            .lock()
            .expect("complete-ledgers mutex must not be poisoned")
            .erase_interval(range(0, seq - 1));
    }

    pub fn complete_ledgers(&self) -> RangeSet<u32> {
        self.complete_ledgers
            .lock()
            .expect("complete-ledgers mutex must not be poisoned")
            .clone()
    }

    pub fn full_validated_range(&self) -> Option<(u32, u32)> {
        let complete_ledgers = self
            .complete_ledgers
            .lock()
            .expect("complete-ledgers mutex must not be poisoned");
        // Match rippled's `getFullValidatedRange`: the advertised upper
        // bound is the published ledger, not the highest fully acquired
        // ledger. Completed inbound candidates may be unvalidated forks and
        // therefore must never extend peer-visible validated/servable range.
        let max = self.published_ledger()?.header().seq;
        if max == 0 {
            return None;
        }

        let min = prev_missing(&complete_ledgers, max, 0).map_or(max, |missing| missing + 1);
        Some((min, max))
    }

    pub fn clear_ledger_cache_prior<P, CLOCK, FB, F, MR, NS, J>(
        &self,
        seq: u32,
        journal: &J,
        config: &LedgerConfig,
        family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
        provider: &P,
    ) -> Result<(), crate::LedgerSetupError>
    where
        P: crate::LedgerInfoProvider,
        CLOCK: CacheClock,
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
        J: LedgerJournal,
    {
        self.ledger_history
            .clear_ledger_cache_prior(seq, journal, config, family, provider)
    }

    pub fn clear_cached_ledger_entries_prior(&self, seq: u32) {
        self.ledger_history.clear_cached_ledger_entries_prior(seq);
    }

    pub fn get_published_ledger_age(&self, now_close_time: u32) -> Duration {
        ledger_age(self.pub_ledger_close.load(Ordering::SeqCst), now_close_time)
    }

    pub fn get_validated_ledger_age(&self, now_close_time: u32) -> Duration {
        ledger_age(
            self.valid_ledger_sign.load(Ordering::SeqCst),
            now_close_time,
        )
    }

    pub fn is_caught_up(&self, now_close_time: u32) -> LedgerMasterCaughtUp {
        if self.get_published_ledger_age(now_close_time) > Duration::minutes(3) {
            return LedgerMasterCaughtUp::No {
                reason: "No recently-published ledger",
            };
        }

        let valid_close = self.valid_ledger_sign.load(Ordering::SeqCst);
        let pub_close = self.pub_ledger_close.load(Ordering::SeqCst);
        if valid_close == 0 || pub_close == 0 {
            return LedgerMasterCaughtUp::No {
                reason: "No published ledger",
            };
        }

        if valid_close > pub_close.saturating_add(90) {
            return LedgerMasterCaughtUp::No {
                reason: "Published ledger lags validated ledger",
            };
        }

        LedgerMasterCaughtUp::Yes
    }

    pub fn new_path_request(&self, requests_pending: bool, is_stopping: bool) -> bool {
        let scheduled = self.new_pf_work(requests_pending, is_stopping);
        self.path_state
            .lock()
            .expect("path-state mutex must not be poisoned")
            .new_request = scheduled;
        scheduled
    }

    pub fn is_new_path_request(&self) -> bool {
        let mut state = self
            .path_state
            .lock()
            .expect("path-state mutex must not be poisoned");
        let ret = state.new_request;
        state.new_request = false;
        ret
    }

    pub fn new_order_book_db(&self, requests_pending: bool, is_stopping: bool) -> bool {
        let mut state = self
            .path_state
            .lock()
            .expect("path-state mutex must not be poisoned");
        state.path_ledger = None;
        drop(state);
        self.new_pf_work(requests_pending, is_stopping)
    }

    pub fn path_ledger(&self) -> Option<Arc<Ledger>> {
        self.path_state
            .lock()
            .expect("path-state mutex must not be poisoned")
            .path_ledger
            .clone()
    }

    pub fn set_path_ledger(&self, ledger: Option<Arc<Ledger>>) {
        self.path_state
            .lock()
            .expect("path-state mutex must not be poisoned")
            .path_ledger = ledger;
    }

    pub fn path_find_thread_count(&self) -> u32 {
        self.path_state
            .lock()
            .expect("path-state mutex must not be poisoned")
            .path_find_threads
    }

    pub fn complete_path_find_job(&self) {
        let mut state = self
            .path_state
            .lock()
            .expect("path-state mutex must not be poisoned");
        if state.path_find_threads > 0 {
            state.path_find_threads -= 1;
        }
        state.path_ledger = None;
    }

    pub fn add_fetch_pack(&self, hash: Uint256, data: Vec<u8>) {
        self.fetch_packs.add_fetch_pack(hash, data);
    }

    pub fn get_fetch_pack(&self, hash: Uint256) -> Option<Vec<u8>> {
        self.fetch_packs.get_fetch_pack(hash)
    }

    /// Match `LedgerMaster::getEarliestFetch`: do not expose a history range
    /// wider than the configured fetch depth behind the current closed ledger.
    pub fn earliest_fetch(&self, fetch_depth: u32) -> u32 {
        self.closed_ledger()
            .map(|ledger| ledger.header().seq.saturating_sub(fetch_depth))
            .unwrap_or_default()
    }

    /// Build rippled's fetch pack for the ledger identified by `have_hash`.
    /// The response walks predecessor history, adding for each predecessor:
    /// header, state-map differences against its child, then its entire
    /// transaction-map difference. The caller owns load/peer admission; this
    /// method owns the ledger-history traversal and exact pack ordering.
    pub fn make_fetch_pack(
        &self,
        have_hash: Uint256,
        earliest_fetch: u32,
        deadline: std::time::Instant,
    ) -> Result<Vec<FetchPackObject>, FetchPackBuildError> {
        self.make_fetch_pack_with_fetcher(have_hash, earliest_fetch, deadline, &|_| None)
    }

    /// Build a FetchPack while resolving released SHAMap nodes through the
    /// caller's durable node-store fetcher. The no-fetch convenience wrapper
    /// above remains useful for fully resident test maps, but serving paths
    /// must use this method so historical state and transaction maps are not
    /// silently truncated.
    pub fn make_fetch_pack_with_fetcher<F>(
        &self,
        have_hash: Uint256,
        earliest_fetch: u32,
        deadline: std::time::Instant,
        node_fetcher: &F,
    ) -> Result<Vec<FetchPackObject>, FetchPackBuildError>
    where
        F: ?Sized
            + Fn(
                SHAMapHash,
            ) -> Option<
                basics::memory::intrusive_pointer::SharedIntrusive<
                    shamap::tree_node::SHAMapTreeNode,
                >,
            >,
    {
        if std::time::Instant::now() > deadline {
            return Err(FetchPackBuildError::Stale);
        }

        let Some(mut have) = self.get_ledger_by_hash(SHAMapHash::new(have_hash)) else {
            return Err(FetchPackBuildError::RequestedLedgerMissing);
        };
        if have.open() {
            return Err(FetchPackBuildError::RequestedLedgerOpen);
        }
        if have.header().seq < earliest_fetch {
            return Err(FetchPackBuildError::RequestedLedgerTooEarly);
        }

        let Some(mut want) = self.get_ledger_by_hash(have.header().parent_hash) else {
            return Err(FetchPackBuildError::RequestedLedgerPredecessorMissing);
        };
        let mut objects = Vec::new();

        loop {
            let sequence = want.header().seq;
            objects.push(FetchPackObject {
                hash: *want.header().hash.as_uint256(),
                data: crate::serialize_prefixed_ledger_header(&want.header(), false),
                ledger_seq: sequence,
            });
            append_fetch_pack_map(
                want.state_map(),
                Some(have.state_map()),
                FETCH_PACK_STATE_NODE_LIMIT,
                sequence,
                node_fetcher,
                &mut objects,
            )
            .map_err(|_| FetchPackBuildError::Traversal)?;
            if want.header().tx_hash.is_non_zero() {
                // Transaction maps are per-ledger. Unlike the state map, do
                // not use the child map as a diff baseline.
                append_fetch_pack_map(
                    want.tx_map(),
                    None,
                    FETCH_PACK_TRANSACTION_NODE_LIMIT,
                    sequence,
                    node_fetcher,
                    &mut objects,
                )
                .map_err(|_| FetchPackBuildError::Traversal)?;
            }

            if objects.len() >= FETCH_PACK_REPLY_CONTINUATION_LIMIT
                || std::time::Instant::now() > deadline
            {
                break;
            }

            have = want;
            let Some(parent) = self.get_ledger_by_hash(have.header().parent_hash) else {
                break;
            };
            want = parent;
        }

        Ok(objects)
    }

    pub fn got_fetch_pack(&self, _progress: bool, _seq: u32) -> bool {
        !self.got_fetch_pack_in_flight.swap(true, Ordering::AcqRel)
    }

    pub fn txn_id_from_index(&self, ledger_seq: u32, txn_index: u32) -> Option<Uint256> {
        let (_, max) = self.full_validated_range()?;
        if ledger_seq > max {
            return None;
        }

        let ledger = self.get_ledger_by_seq(ledger_seq, &NullLedgerJournal)?;
        let txs = ledger.tx_snapshot().ok()?;

        txs.into_iter()
            .find(|(_, meta)| meta.get_index() == txn_index)
            .map(|(txn, _)| txn.get_transaction_id())
    }

    fn fix_mismatch(&self, ledger: &Ledger) {
        for seq in (1..ledger.header().seq).rev() {
            if !self.have_ledger(seq) {
                continue;
            }

            let Some(expected_hash) = ledger.hash_of_seq(seq, &NullLedgerJournal) else {
                self.clear_ledger(seq);
                continue;
            };

            match self.get_ledger_by_seq(seq, &NullLedgerJournal) {
                Some(other) if other.header().hash == expected_hash => return,
                _ => {
                    self.clear_ledger(seq);
                }
            }
        }
    }

    pub fn finish_got_fetch_pack(&self) {
        self.got_fetch_pack_in_flight
            .store(false, Ordering::Release);
    }

    pub fn get_fetch_pack_cache_size(&self) -> usize {
        self.fetch_packs.get_cache_size()
    }

    pub fn sweep(&self)
    where
        LedgerHistory<C, S>: LedgerMasterSweepTarget,
        FetchPackCache<C, S>: LedgerMasterSweepTarget,
    {
        sweep_ledger_master_like(&self.ledger_history, self.fetch_packs.as_ref());
    }

    fn new_pf_work(&self, requests_pending: bool, is_stopping: bool) -> bool {
        let mut state = self
            .path_state
            .lock()
            .expect("path-state mutex must not be poisoned");
        if !is_stopping
            && state.path_find_threads < self.config.path_find_job_limit
            && requests_pending
        {
            state.path_find_threads += 1;
        }

        state.path_find_threads > 0 && !is_stopping
    }
}

fn append_fetch_pack_map<F>(
    want: &shamap::sync::SyncTree,
    have: Option<&shamap::sync::SyncTree>,
    limit: usize,
    ledger_seq: u32,
    node_fetcher: &F,
    objects: &mut Vec<FetchPackObject>,
) -> Result<(), TraversalError>
where
    F: ?Sized
        + Fn(
            SHAMapHash,
        ) -> Option<
            basics::memory::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>,
        >,
{
    debug_assert_ne!(limit, 0);
    let want_root = want.root();
    let have_root = have.map(shamap::sync::SyncTree::root);
    let have_backed = have.is_some_and(shamap::sync::SyncTree::backed);
    let mut want_fetch = |hash| node_fetcher(hash);
    let mut have_fetch = |hash| node_fetcher(hash);
    let mut added = 0usize;

    shamap::difference::visit_differences(
        &want_root,
        have_root.as_ref(),
        want.backed(),
        &mut want_fetch,
        have_backed,
        &mut have_fetch,
        &mut |node: &basics::memory::intrusive_pointer::SharedIntrusive<
            shamap::tree_node::SHAMapTreeNode,
        >| {
            let Ok(data) = node.serialize_with_prefix() else {
                return true;
            };
            objects.push(FetchPackObject {
                hash: *node.get_hash().as_uint256(),
                data,
                ledger_seq,
            });
            added += 1;
            added < limit
        },
    )
}

fn ledger_age(stored_close_time: u32, now_close_time: u32) -> Duration {
    if stored_close_time == 0 {
        return Duration::weeks(2);
    }

    Duration::seconds(i64::from(now_close_time.saturating_sub(stored_close_time)))
}

fn close_time_distance(first: u32, second: u32) -> Duration {
    Duration::seconds(i64::from(first.abs_diff(second)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{LedgerHeader, LedgerPersistenceRuntime, NullLedgerJournal, calculate_ledger_hash};
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::SharedIntrusive;
    use protocol::{
        AccountID, STAmount, STArray, STObject, STTx, Serializer, TxType, get_field_by_symbol,
    };
    use shamap::item::SHAMapItem;
    use shamap::sync::{SHAMapType, SyncState, SyncTree};
    use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};

    struct NoopPersistenceRuntime;

    impl LedgerPersistenceRuntime for NoopPersistenceRuntime {
        fn mark_saved(&self, _hash: basics::sha_map_hash::SHAMapHash) -> bool {
            true
        }

        fn start_work(&self, _seq: u32) -> bool {
            true
        }

        fn finish_work(&self, _seq: u32) {}

        fn should_work(&self, _seq: u32, _is_synchronous: bool) -> bool {
            true
        }

        fn pending(&self, _seq: u32) -> bool {
            false
        }

        fn save_validated_ledger(&self, _ledger: Arc<Ledger>, _is_current: bool) -> bool {
            true
        }

        fn enqueue_job(
            &self,
            _job_type: crate::LedgerPersistenceJobType,
            _job_name: String,
            _job: crate::persistence::LedgerPersistenceJob,
        ) -> bool {
            true
        }
    }

    fn state_leaf(fill: u8) -> SharedIntrusive<SHAMapTreeNode> {
        SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([fill; 32]), vec![fill; 12]),
            0,
        )
    }

    fn account(fill: u8) -> AccountID {
        AccountID::from_array([fill; 20])
    }

    fn payment_tx(sequence: u32, account_fill: u8, destination_fill: u8) -> Arc<STTx> {
        Arc::new(STTx::new(TxType::PAYMENT, |tx| {
            tx.set_account_id(get_field_by_symbol("sfAccount"), account(account_fill));
            tx.set_account_id(
                get_field_by_symbol("sfDestination"),
                account(destination_fill),
            );
            tx.set_field_amount(
                get_field_by_symbol("sfAmount"),
                STAmount::new_native(1_000_000, false),
            );
            tx.set_field_amount(
                get_field_by_symbol("sfFee"),
                STAmount::new_native(10, false),
            );
            tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        }))
    }

    fn metadata(index: u32, fill: u8) -> STObject {
        let mut final_fields = STObject::new(get_field_by_symbol("sfFinalFields"));
        final_fields.set_account_id(get_field_by_symbol("sfAccount"), account(fill));

        let mut node = STObject::new(get_field_by_symbol("sfModifiedNode"));
        node.set_field_h256(
            get_field_by_symbol("sfLedgerIndex"),
            Uint256::from_array([fill; 32]),
        );
        node.set_field_u16(get_field_by_symbol("sfLedgerEntryType"), 97);
        node.set_field_object(get_field_by_symbol("sfFinalFields"), final_fields);

        let mut affected_nodes = STArray::new(get_field_by_symbol("sfAffectedNodes"));
        affected_nodes.push_back(node);

        let mut meta = STObject::new(get_field_by_symbol("sfTransactionMetaData"));
        meta.set_field_u8(get_field_by_symbol("sfTransactionResult"), 0);
        meta.set_field_u32(get_field_by_symbol("sfTransactionIndex"), index);
        meta.set_field_array(get_field_by_symbol("sfAffectedNodes"), affected_nodes);
        meta
    }

    fn tx_md_payload(tx: &STTx, meta: &STObject) -> Vec<u8> {
        let tx_bytes = tx.get_serializer().data().to_vec();
        let meta_bytes = meta.get_serializer().data().to_vec();
        let mut serializer = Serializer::new(0);
        serializer.add_vl(&tx_bytes);
        serializer.add_vl(&meta_bytes);
        serializer.data().to_vec()
    }

    fn closed_ledger_with_txs(items: &[(Arc<STTx>, STObject)], seq: u32) -> Arc<Ledger> {
        let root = state_leaf(seq as u8);
        let mut tree = shamap::mutation::MutableTree::new(seq);
        for (tx, meta) in items {
            tree.add_item(
                SHAMapNodeType::TransactionMd,
                SHAMapItem::new(tx.get_transaction_id(), tx_md_payload(tx, meta)),
            )
            .expect("transaction-with-metadata item should insert");
        }

        let mut header = LedgerHeader {
            seq,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);

        let mut ledger = Ledger::from_maps(
            header,
            SyncTree::from_root_with_type(
                root,
                SHAMapType::State,
                false,
                seq,
                SyncState::Immutable,
            ),
            SyncTree::from_root_with_type(
                tree.root(),
                SHAMapType::Transaction,
                false,
                seq,
                SyncState::Immutable,
            ),
        );
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    fn immutable_ledger(seq: u32, fill: u8) -> Arc<Ledger> {
        let root = state_leaf(fill);
        let mut header = LedgerHeader {
            seq,
            account_hash: root.get_hash(),
            parent_hash: crate::SHAMapHash::new(Uint256::from_array([fill.wrapping_add(1); 32])),
            close_time: seq + 100,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);
        let mut ledger = Ledger::from_maps(
            header,
            SyncTree::from_root_with_type(root, SHAMapType::State, true, seq, SyncState::Modifying),
            SyncTree::new_with_type(SHAMapType::Transaction, true, seq),
        );
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    fn linked_ledger(previous: &Arc<Ledger>, close_time: u32) -> Arc<Ledger> {
        let mut ledger = Ledger::from_previous(previous, close_time);
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    fn ledger_with_maps(
        seq: u32,
        parent: &Arc<Ledger>,
        state_fill: u8,
        tx_fill: Option<u8>,
    ) -> Arc<Ledger> {
        let state_root = state_leaf(state_fill);
        let tx_root = tx_fill.map(|fill| {
            SHAMapTreeNode::new_leaf(
                SHAMapNodeType::TransactionNm,
                SHAMapItem::new(Uint256::from_array([fill; 32]), vec![fill; 12]),
                0,
            )
        });
        let mut header = LedgerHeader {
            seq,
            account_hash: state_root.get_hash(),
            tx_hash: tx_root
                .as_ref()
                .map(|root| root.get_hash())
                .unwrap_or_default(),
            parent_hash: parent.header().hash,
            close_time: seq + 100,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);
        let mut ledger = Ledger::from_maps(
            header,
            SyncTree::from_root_with_type(
                state_root,
                SHAMapType::State,
                true,
                seq,
                SyncState::Immutable,
            ),
            tx_root.map_or_else(
                || SyncTree::new_with_type(SHAMapType::Transaction, true, seq),
                |root| {
                    SyncTree::from_root_with_type(
                        root,
                        SHAMapType::Transaction,
                        true,
                        seq,
                        SyncState::Immutable,
                    )
                },
            ),
        );
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    #[test]
    fn master_tracks_published_and_validated_age() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let ledger = immutable_ledger(25, 0x11);

        master.set_pub_ledger(Arc::clone(&ledger));
        master
            .set_valid_ledger(
                Arc::clone(&ledger),
                None,
                Some(ledger.header().close_time + 10),
            )
            .expect("validated ledger update should not fail");

        assert_eq!(
            master.get_published_ledger_age(ledger.header().close_time + 30),
            Duration::seconds(30)
        );
        assert_eq!(
            master.get_validated_ledger_age(ledger.header().close_time + 30),
            Duration::seconds(20)
        );
    }

    #[test]
    fn make_fetch_pack_assembles_predecessor_header_then_state_and_transaction_nodes() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let oldest = immutable_ledger(40, 0x01);
        let want = ledger_with_maps(41, &oldest, 0x41, Some(0x51));
        let have = ledger_with_maps(42, &want, 0x42, Some(0x52));
        master.ledger_history().insert(Arc::clone(&oldest), false);
        master.ledger_history().insert(Arc::clone(&want), false);
        master.ledger_history().insert(Arc::clone(&have), false);
        master.set_closed_ledger(Arc::clone(&have));

        let objects = master
            .make_fetch_pack(
                *have.header().hash.as_uint256(),
                master.earliest_fetch(16),
                std::time::Instant::now() + std::time::Duration::from_secs(1),
            )
            .expect("fetch pack should assemble from local predecessor history");

        assert!(objects.len() >= 3, "header plus state and tx map nodes");
        assert_eq!(objects[0].hash, *want.header().hash.as_uint256());
        assert_eq!(objects[0].ledger_seq, want.header().seq);
        assert_eq!(
            objects[0].data,
            crate::serialize_prefixed_ledger_header(&want.header(), false),
            "each predecessor starts with its prefixed ledger header"
        );
        assert_eq!(objects[1].ledger_seq, want.header().seq);
        assert_eq!(
            objects[1].hash,
            *want.state_map().root().get_hash().as_uint256()
        );
        assert_eq!(objects[2].ledger_seq, want.header().seq);
        assert_eq!(
            objects[2].hash,
            *want.tx_map().root().get_hash().as_uint256()
        );
        assert_eq!(
            objects[3].hash,
            *oldest.header().hash.as_uint256(),
            "the pack continues with the next predecessor only after the first ledger's maps"
        );
        assert_eq!(objects[3].ledger_seq, oldest.header().seq);
    }

    #[test]
    fn make_fetch_pack_enforces_staleness_and_earliest_fetch_eligibility() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let old = immutable_ledger(10, 0x01);
        let have = linked_ledger(&old, 120);
        master.ledger_history().insert(Arc::clone(&old), false);
        master.ledger_history().insert(Arc::clone(&have), false);
        master.set_closed_ledger(Arc::clone(&have));

        assert_eq!(
            master.make_fetch_pack(
                *have.header().hash.as_uint256(),
                12,
                std::time::Instant::now() + std::time::Duration::from_secs(1),
            ),
            Err(FetchPackBuildError::RequestedLedgerTooEarly)
        );
        assert_eq!(
            master.make_fetch_pack(
                *have.header().hash.as_uint256(),
                0,
                std::time::Instant::now() - std::time::Duration::from_millis(1),
            ),
            Err(FetchPackBuildError::Stale)
        );
        assert_eq!(master.earliest_fetch(1), have.header().seq - 1);
        assert_eq!(
            master.make_fetch_pack(
                Uint256::from_u64(0xDEAD),
                0,
                std::time::Instant::now() + std::time::Duration::from_secs(1),
            ),
            Err(FetchPackBuildError::RequestedLedgerMissing)
        );

        let absent_parent = immutable_ledger(90, 0xBA);
        let have_without_parent = linked_ledger(&absent_parent, 91);
        master
            .ledger_history()
            .insert(Arc::clone(&have_without_parent), false);
        assert_eq!(
            master.make_fetch_pack(
                *have_without_parent.header().hash.as_uint256(),
                0,
                std::time::Instant::now() + std::time::Duration::from_secs(1),
            ),
            Err(FetchPackBuildError::RequestedLedgerPredecessorMissing),
            "an initial missing predecessor cannot produce a pack"
        );
    }

    #[test]
    fn master_path_request_and_fetch_pack_dispatch_are_single_flight() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());

        assert!(master.new_path_request(true, false));
        assert!(master.is_new_path_request());
        assert!(!master.is_new_path_request());
        assert_eq!(master.path_find_thread_count(), 1);
        master.complete_path_find_job();
        assert_eq!(master.path_find_thread_count(), 0);

        assert!(master.got_fetch_pack(false, 10));
        assert!(!master.got_fetch_pack(false, 10));
        master.finish_got_fetch_pack();
        assert!(master.got_fetch_pack(false, 10));
    }

    #[test]
    fn full_validated_range_stops_at_published_ledger_not_acquired_fork() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let published = immutable_ledger(100, 0x10);
        let acquired_unvalidated = immutable_ledger(101, 0x20);

        master.set_pub_ledger(Arc::clone(&published));
        master.mark_ledger_complete(published.header().seq);
        master.mark_ledger_complete(acquired_unvalidated.header().seq);

        assert_eq!(master.full_validated_range(), Some((100, 100)));
    }

    #[test]
    fn master_set_full_ledger_marks_complete_and_updates_holders() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let persistence = LedgerPersistence::new(Arc::new(NoopPersistenceRuntime));
        let ledger = immutable_ledger(30, 0x22);

        let saved = master
            .set_full_ledger(&persistence, Arc::clone(&ledger), true, true, None, None)
            .expect("full ledger orchestration should not fail");

        assert!(saved);
        assert!(master.have_ledger(30));
        assert_eq!(
            master
                .validated_ledger()
                .expect("validated ledger")
                .header()
                .hash,
            ledger.header().hash
        );
        assert_eq!(
            master
                .published_ledger()
                .expect("published ledger")
                .header()
                .hash,
            ledger.header().hash
        );
    }

    #[test]
    fn master_check_accept_ledger_preserves_cpp_can_be_current_gates() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let valid = immutable_ledger(100, 0x10);
        master
            .set_valid_ledger(Arc::clone(&valid), None, None)
            .expect("valid ledger should update");

        let acceptable = linked_ledger(&valid, valid.header().close_time + 10);
        assert!(master.check_accept_ledger(
            acceptable.as_ref(),
            3,
            2,
            valid.header().parent_close_time + 20
        ));
        assert!(!master.check_accept_ledger(
            acceptable.as_ref(),
            1,
            2,
            valid.header().parent_close_time + 20
        ));

        let stale = immutable_ledger(99, 0x20);
        assert!(!master.check_accept_ledger(
            stale.as_ref(),
            3,
            2,
            valid.header().parent_close_time + 20
        ));

        let mut far_future = Ledger::from_previous(valid.as_ref(), valid.header().close_time + 10);
        far_future.set_ledger_info(LedgerHeader {
            seq: 10_000,
            ..far_future.header()
        });
        let far_future = Arc::new(far_future);
        assert!(!master.check_accept_ledger(
            far_future.as_ref(),
            3,
            2,
            valid.header().parent_close_time + 20
        ));

        assert!(!master.check_accept_ledger(
            acceptable.as_ref(),
            3,
            2,
            acceptable.header().parent_close_time + 301
        ));
    }

    #[test]
    fn master_cached_lookups_match_cpp_hash_and_sequence_fallbacks() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let parent = immutable_ledger(31, 0x33);
        let child = linked_ledger(&parent, 111);

        master.set_closed_ledger(Arc::clone(&parent));
        assert!(Arc::ptr_eq(
            &master
                .get_ledger_by_hash(parent.header().hash)
                .expect("closed-ledger hash lookup"),
            &parent
        ));

        master.ledger_history().insert(Arc::clone(&parent), true);
        master
            .set_valid_ledger(Arc::clone(&child), None, None)
            .expect("valid ledger should update");

        assert!(Arc::ptr_eq(
            &master
                .get_ledger_by_seq(child.header().seq, &NullLedgerJournal)
                .expect("validated seq lookup"),
            &child
        ));
        assert!(Arc::ptr_eq(
            &master
                .get_ledger_by_seq(parent.header().seq, &NullLedgerJournal)
                .expect("validated parent lookup"),
            &parent
        ));
    }

    #[test]
    fn master_txn_id_from_index_lookup_shape() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let expected_tx = payment_tx(2, 0x21, 0x31);
        let ledger = closed_ledger_with_txs(
            &[
                (payment_tx(3, 0x31, 0x41), metadata(9, 0x91)),
                (payment_tx(1, 0x11, 0x21), metadata(2, 0x92)),
                (Arc::clone(&expected_tx), metadata(5, 0x93)),
            ],
            88,
        );
        let persistence = LedgerPersistence::new(Arc::new(NoopPersistenceRuntime));

        master
            .set_full_ledger(&persistence, Arc::clone(&ledger), true, true, None, None)
            .expect("full ledger orchestration should not fail");

        assert_eq!(
            master.txn_id_from_index(ledger.header().seq, 5),
            Some(expected_tx.get_transaction_id())
        );
        assert_eq!(master.txn_id_from_index(ledger.header().seq, 8), None);
        assert_eq!(master.txn_id_from_index(ledger.header().seq + 1, 5), None);
    }
}
