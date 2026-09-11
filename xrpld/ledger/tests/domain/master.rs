use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::MonotonicClock;
use ledger::master::LEDGER_MASTER_MAX_PUBLISH_GAP;
use ledger::{
    Ledger, LedgerHeader, LedgerMaster, LedgerMasterConfig, LedgerPersistence,
    LedgerPersistenceRuntime, calculate_ledger_hash,
};
use protocol::{AccountID, STAmount, STTx, TxType, get_field_by_symbol};
use shamap::item::SHAMapItem;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use std::sync::Arc;

fn sample_hash(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

fn account(hex: &str) -> AccountID {
    AccountID::from_hex(hex).expect("account hex should parse")
}

fn payment_tx(
    source: AccountID,
    destination: AccountID,
    sequence: u32,
    ticket_sequence: Option<u32>,
    fee_drops: u64,
) -> Arc<STTx> {
    Arc::new(STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        if let Some(ticket_sequence) = ticket_sequence {
            tx.set_field_u32(get_field_by_symbol("sfTicketSequence"), ticket_sequence);
        }
    }))
}

fn state_leaf(fill: u8) -> SharedIntrusive<SHAMapTreeNode> {
    SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_hash(fill), vec![fill; 12]),
        0,
    )
}

fn immutable_ledger(seq: u32, parent_fill: u8, account_fill: u8) -> Arc<Ledger> {
    let root = state_leaf(account_fill);
    let mut header = LedgerHeader {
        seq,
        account_hash: root.get_hash(),
        parent_hash: SHAMapHash::new(sample_hash(parent_fill)),
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

#[derive(Debug, Default)]
struct NoopPersistenceRuntime;

impl LedgerPersistenceRuntime for NoopPersistenceRuntime {
    fn mark_saved(&self, _hash: SHAMapHash) -> bool {
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
        _job_type: ledger::LedgerPersistenceJobType,
        _job_name: String,
        _job: ledger::LedgerPersistenceJob,
    ) -> bool {
        true
    }
}

#[derive(Debug, Default)]
struct FailingPersistenceRuntime;

impl LedgerPersistenceRuntime for FailingPersistenceRuntime {
    fn mark_saved(&self, _hash: SHAMapHash) -> bool {
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
        false
    }

    fn enqueue_job(
        &self,
        _job_type: ledger::LedgerPersistenceJobType,
        _job_name: String,
        _job: ledger::LedgerPersistenceJob,
    ) -> bool {
        false
    }
}

#[test]
fn set_full_ledger_retracts_complete_range_when_sync_save_fails() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let persistence = LedgerPersistence::new(Arc::new(FailingPersistenceRuntime));
    let ledger = immutable_ledger(33, 0x21, 0x33);

    assert!(
        !master
            .set_full_ledger(&persistence, Arc::clone(&ledger), true, false, None, None)
            .expect("failed persistence is a result, not a traversal error")
    );
    assert!(
        !master.have_ledger(33),
        "a ledger whose synchronous save failed must not remain complete"
    );
}

#[test]
fn set_full_ledger_clears_mismatched_previous_sequence() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let persistence = LedgerPersistence::new(Arc::new(NoopPersistenceRuntime));
    let older = immutable_ledger(29, 0x11, 0x30);
    let previous = immutable_ledger(30, 0x21, 0x31);
    let current = immutable_ledger(31, 0x99, 0x32);

    master.ledger_history().insert(older.clone(), true);
    master.mark_ledger_complete(older.header().seq);
    master.ledger_history().insert(previous.clone(), true);
    master.mark_ledger_complete(previous.header().seq);

    assert!(master.have_ledger(older.header().seq));
    assert!(master.have_ledger(previous.header().seq));

    let saved = master
        .set_full_ledger(&persistence, Arc::clone(&current), true, true, None, None)
        .expect("full ledger orchestration should not fail");

    assert!(saved);
    assert!(!master.have_ledger(older.header().seq));
    assert!(!master.have_ledger(previous.header().seq));
    assert!(master.have_ledger(current.header().seq));
    let validated = master.validated_ledger().expect("validated ledger");
    assert!(validated.header().validated);
    assert!(validated.state_map().is_full());
    assert!(validated.tx_map().is_full());
    assert_eq!(validated.header().hash, current.header().hash);
    assert_eq!(
        master
            .published_ledger()
            .expect("published ledger")
            .header()
            .hash,
        current.header().hash
    );
}

#[test]
fn ledger_master_add_and_pop_held_transactions_follow_canonical_account_rules() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let source = account("1111111111111111111111111111111111111111");
    let current = payment_tx(
        source,
        account("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"),
        5,
        None,
        10,
    );
    let next = payment_tx(
        source,
        account("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB"),
        6,
        None,
        11,
    );
    let later_ticket = payment_tx(
        source,
        account("CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC"),
        0,
        Some(2),
        12,
    );

    master.add_held_transaction(Arc::clone(&later_ticket));
    master.add_held_transaction(Arc::clone(&next));

    assert_eq!(master.held_transaction_count(), 2);

    let popped = master
        .pop_acct_transaction(&current)
        .expect("next sequence should pop before tickets");
    assert_eq!(popped.get_transaction_id(), next.get_transaction_id());
    assert_eq!(master.held_transaction_count(), 1);

    let popped_ticket = master
        .pop_acct_transaction(&next)
        .expect("lowest ticket should pop after sequential txs");
    assert_eq!(
        popped_ticket.get_transaction_id(),
        later_ticket.get_transaction_id()
    );
    assert_eq!(master.held_transaction_count(), 0);
}

#[test]
fn ledger_master_apply_held_transactions_drains_once_and_rolls_next_salt() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let source = account("2222222222222222222222222222222222222222");
    let first = payment_tx(
        source,
        account("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"),
        1,
        None,
        10,
    );
    let second = payment_tx(
        source,
        account("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB"),
        2,
        None,
        11,
    );

    master.add_held_transaction(Arc::clone(&second));
    master.add_held_transaction(Arc::clone(&first));

    let mut seen = Vec::new();
    let drained = master.apply_held_transactions(Uint256::from_u64(77), |set| {
        seen = set.iter().map(|tx| tx.get_transaction_id()).collect();
        assert_eq!(set.key(), Uint256::zero());
    });

    assert_eq!(drained, 2);
    assert_eq!(
        seen,
        vec![first.get_transaction_id(), second.get_transaction_id()]
    );
    assert_eq!(master.held_transaction_count(), 0);

    let third = payment_tx(
        source,
        account("CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC"),
        3,
        None,
        12,
    );
    master.add_held_transaction(Arc::clone(&third));

    let drained = master.apply_held_transactions(Uint256::from_u64(88), |set| {
        assert_eq!(set.key(), Uint256::from_u64(77));
        let ids: Vec<_> = set.iter().map(|tx| tx.get_transaction_id()).collect();
        assert_eq!(ids, vec![third.get_transaction_id()]);
    });

    assert_eq!(drained, 1);
    assert_eq!(master.held_transaction_count(), 0);
}

#[test]
fn ledger_master_apply_held_transactions_skips_callback_when_empty() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let mut called = false;

    let drained = master.apply_held_transactions(Uint256::from_u64(90), |_| {
        called = true;
    });

    assert_eq!(drained, 0);
    assert!(!called);
    assert_eq!(master.held_transaction_count(), 0);
}

#[test]
fn do_advance_first_publish_uses_validated_ledger_without_history_backfill() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let validated = immutable_ledger(40, 0x10, 0x40);

    master
        .set_valid_ledger(Arc::clone(&validated), None, None)
        .expect("valid ledger should update");

    assert_eq!(master.do_advance(), 1);
    assert_eq!(
        master
            .published_ledger()
            .expect("published ledger should be set on first publish")
            .header()
            .hash,
        validated.header().hash
    );
}

#[test]
fn do_advance_large_validated_gap_publishes_only_latest() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let published = immutable_ledger(10, 0x20, 0x50);
    let mut validated = Arc::clone(&published);
    for close_time in 111..=(111 + LEDGER_MASTER_MAX_PUBLISH_GAP) {
        validated = linked_ledger(&validated, close_time);
    }
    let validated = linked_ledger(&validated, 500);

    master.set_pub_ledger(Arc::clone(&published));
    master
        .set_valid_ledger(Arc::clone(&validated), None, None)
        .expect("valid ledger should update");

    assert_eq!(
        validated.header().seq,
        published.header().seq + LEDGER_MASTER_MAX_PUBLISH_GAP + 2
    );
    assert_eq!(master.do_advance(), 1);
    assert_eq!(
        master
            .published_ledger()
            .expect("published ledger should jump to the latest validated ledger")
            .header()
            .hash,
        validated.header().hash
    );
}

#[test]
fn do_advance_waits_for_missing_intermediate_history() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let published = immutable_ledger(20, 0x30, 0x60);
    let ledger_21 = linked_ledger(&published, 121);
    let validated = linked_ledger(&ledger_21, 122);

    master.set_pub_ledger(Arc::clone(&published));
    master
        .set_valid_ledger(Arc::clone(&validated), None, None)
        .expect("valid ledger should update");

    assert_eq!(master.do_advance(), 0);
    assert_eq!(
        master
            .published_ledger()
            .expect("published ledger should stay put until the next contiguous ledger is cached")
            .header()
            .hash,
        published.header().hash
    );
}

#[test]
fn set_full_ledger_keeps_history_backfill_separate_from_published_and_validated() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let persistence = LedgerPersistence::new(Arc::new(NoopPersistenceRuntime));
    let published = immutable_ledger(50, 0x40, 0x70);
    let historical = immutable_ledger(45, 0x41, 0x71);

    master.set_pub_ledger(Arc::clone(&published));
    master
        .set_valid_ledger(Arc::clone(&published), None, None)
        .expect("valid ledger should update");

    master
        .set_full_ledger(
            &persistence,
            Arc::clone(&historical),
            true,
            false,
            None,
            None,
        )
        .expect("historical ledger caching should not fail");

    assert!(master.have_ledger(historical.header().seq));
    assert_eq!(
        master
            .validated_ledger()
            .expect("validated ledger should remain unchanged")
            .header()
            .hash,
        published.header().hash
    );
    assert_eq!(
        master
            .published_ledger()
            .expect("published ledger should remain unchanged")
            .header()
            .hash,
        published.header().hash
    );
}

#[test]
fn last_valid_ledger_rejects_conflicting_cached_and_acquired_lcl_candidates() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let quorum_backed = immutable_ledger(40, 0x10, 0x40);
    master.note_last_valid_ledger(
        *quorum_backed.header().hash.as_uint256(),
        quorum_backed.header().seq,
    );

    let compatible = linked_ledger(&quorum_backed, 141);
    let cached_conflict = immutable_ledger(41, 0x99, 0x41);
    let acquired_conflict = immutable_ledger(42, 0x98, 0x42);
    master
        .ledger_history()
        .insert(Arc::clone(&cached_conflict), false);

    assert_eq!(
        master.last_valid_ledger(),
        Some((*quorum_backed.header().hash.as_uint256(), 40))
    );
    let compatible_audit = master.compatibility_audit(compatible.as_ref());
    assert!(compatible_audit.compatible());
    assert!(
        compatible_audit
            .last_valid_anchor
            .is_some_and(|anchor| anchor.matches)
    );
    assert!(master.is_compatible(compatible.as_ref()));
    assert!(
        master
            .ledger_history()
            .get_cached_ledger_by_hash(cached_conflict.header().hash)
            .is_some()
    );
    let cached_conflict_audit = master.compatibility_audit(cached_conflict.as_ref());
    assert!(!cached_conflict_audit.compatible());
    assert!(
        cached_conflict_audit
            .last_valid_anchor
            .is_some_and(|anchor| !anchor.matches)
    );
    assert!(!master.is_compatible(cached_conflict.as_ref()));
    // Acquired candidates take the identical guard after they enter the
    // history cache; a conflicting acquired parent is still rejected.
    assert!(!master.is_compatible(acquired_conflict.as_ref()));
}

#[test]
fn set_full_ledger_current_acquisition_advances_validated_before_publish() {
    let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
    let persistence = LedgerPersistence::new(Arc::new(NoopPersistenceRuntime));
    let published = immutable_ledger(60, 0x50, 0x80);
    let validated = linked_ledger(&published, 161);

    master.set_pub_ledger(Arc::clone(&published));
    master
        .set_valid_ledger(Arc::clone(&published), None, None)
        .expect("valid ledger should update");

    master
        .set_full_ledger(&persistence, Arc::clone(&validated), true, true, None, None)
        .expect("current completed acquisition should not fail");

    assert_eq!(
        master
            .validated_ledger()
            .expect("validated ledger should advance immediately")
            .header()
            .hash,
        validated.header().hash
    );
    assert_eq!(
        master
            .published_ledger()
            .expect("published ledger should remain unchanged until do_advance")
            .header()
            .hash,
        published.header().hash
    );

    assert_eq!(master.do_advance(), 1);
    assert_eq!(
        master
            .published_ledger()
            .expect("published ledger should catch up after advancement")
            .header()
            .hash,
        validated.header().hash
    );
}
