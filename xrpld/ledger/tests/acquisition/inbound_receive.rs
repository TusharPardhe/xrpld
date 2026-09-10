use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::ledger_fetcher::INBOUND_LEDGER_MAX_PACKET_NODES_PER_STEP;
use ledger::{
    InboundLedgerCompletionDisposition, InboundLedgerDataType, InboundLedgerJournal,
    InboundLedgerLocal, InboundLedgerNodeData, InboundLedgerPacket, InboundLedgerPacketError,
    InboundLedgerStore, LedgerConfig, LedgerHeader, XRP_LEDGER_EARLIEST_FEES,
    calculate_ledger_hash,
};
use shamap::family::{NullFullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily};
use shamap::item::SHAMapItem;
use shamap::node_id::SHAMapNodeId;
use shamap::storage::{NodeObjectType, StoredNode};
use shamap::sync::{SHAMapAddNode, SyncState};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;
use time::Duration;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

#[derive(Debug, Default)]
struct RecordingInboundStore {
    headers: Rc<RefCell<HashMap<Uint256, Blob>>>,
    stored_headers: Rc<RefCell<Vec<(Uint256, u32, Blob)>>>,
    stored_nodes: Rc<RefCell<Vec<StoredNode>>>,
}

impl InboundLedgerStore for RecordingInboundStore {
    fn fetch_ledger_header(&mut self, hash: SHAMapHash, _ledger_seq: u32) -> Option<Blob> {
        self.headers.borrow().get(hash.as_uint256()).cloned()
    }

    fn store_ledger_header(&mut self, data: Blob, hash: SHAMapHash, ledger_seq: u32) {
        self.headers
            .borrow_mut()
            .insert(*hash.as_uint256(), data.clone());
        self.stored_headers
            .borrow_mut()
            .push((*hash.as_uint256(), ledger_seq, data));
    }

    fn store_shamap_node(
        &mut self,
        object_type: NodeObjectType,
        data: Blob,
        hash: Uint256,
        ledger_seq: u32,
    ) {
        self.stored_nodes
            .borrow_mut()
            .push(StoredNode::new(object_type, data, hash, ledger_seq));
    }
}

#[derive(Debug, Default)]
struct RecordingFetchPack {
    blobs: Rc<RefCell<HashMap<Uint256, Blob>>>,
}

impl ledger::FetchPackContainer for RecordingFetchPack {
    fn get_fetch_pack(&mut self, hash: Uint256) -> Option<Blob> {
        self.blobs.borrow().get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingJournal {
    traces: RefCell<Vec<String>>,
    warns: RefCell<Vec<String>>,
}

impl InboundLedgerJournal for RecordingJournal {
    fn trace(&self, message: &str) {
        self.traces.borrow_mut().push(message.to_owned());
    }

    fn debug(&self, _message: &str) {}

    fn warn(&self, message: &str) {
        self.warns.borrow_mut().push(message.to_owned());
    }

    fn fatal(&self, _message: &str) {}
}

fn family(
    label: &'static str,
) -> SHAMapFamily<
    ManualClock,
    basics::hardened_hash::HardenedHashBuilder,
    NullFullBelowCache,
    NullNodeFetcher,
    NullMissingNodeReporter,
> {
    SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            label,
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
    )
}

fn sample_header(seq: u32, account_hash: SHAMapHash, tx_hash: SHAMapHash) -> LedgerHeader {
    LedgerHeader {
        seq,
        drops: 55,
        parent_hash: sample_hash(0x01),
        account_hash,
        tx_hash,
        parent_close_time: 22,
        close_time: 33,
        close_time_resolution: 30,
        close_flags: 0,
        ..LedgerHeader::default()
    }
}

fn raw_header_bytes(header: &LedgerHeader) -> Blob {
    let prefixed = ledger::serialize_prefixed_ledger_header(header, false);
    prefixed[4..].to_vec()
}

fn prefixed_header_bytes(header: &LedgerHeader) -> Blob {
    ledger::serialize_prefixed_ledger_header(header, false)
}

#[test]
fn inbound_take_header_sets_cpp_owner_flags_and_synching() {
    let header = sample_header(600, sample_hash(0x31), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let journal = RecordingJournal::default();

    let accepted = inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    );

    assert!(accepted);
    assert_eq!(inbound.seq(), 600);
    assert!(inbound.planner_state().have_header);
    assert!(inbound.planner_state().have_transactions);
    assert!(!inbound.planner_state().have_state);
    let ledger = inbound
        .ledger()
        .expect("accepted header should create a ledger");
    assert_eq!(ledger.tx_map().state(), SyncState::Modifying);
    assert_eq!(ledger.state_map().state(), SyncState::Synching);
    assert_eq!(store.stored_headers.borrow().len(), 1);
}

#[test]
fn inbound_try_db_header_load_arms_cpp_owner_flags_and_synching() {
    let header = sample_header(600, sample_hash(0x35), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();
    let journal = RecordingJournal::default();
    let family = family("inbound-try-db-header");

    store
        .headers
        .borrow_mut()
        .insert(*wanted_hash.as_uint256(), prefixed_header_bytes(&header));

    inbound.try_db_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );

    assert!(inbound.planner_state().have_header);
    assert!(inbound.planner_state().have_transactions);
    assert!(!inbound.planner_state().have_state);
    let ledger = inbound.ledger().expect("try_db should load the header");
    assert_eq!(ledger.tx_map().state(), SyncState::Modifying);
    assert_eq!(ledger.state_map().state(), SyncState::Synching);
}

#[test]
fn inbound_revalidate_does_not_reopen_zero_tx_root_completion() {
    let header = sample_header(600, sample_hash(0x61), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-revalidate-zero-tx");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));

    assert!(inbound.planner_state().have_transactions);
    assert!(!inbound.revalidate_map_sync_with_family(&family));
    assert!(inbound.planner_state().have_transactions);
    assert!(!inbound.is_complete());
}

#[test]
fn inbound_revalidate_can_finalize_completion_from_map_state_trigger() {
    let header = sample_header(600, sample_hash(0x71), sample_hash(0x72));
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-revalidate-finish");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));

    let ledger = inbound
        .ledger_mut()
        .expect("header load should create the working ledger");
    ledger.state_map_mut().clear_synching();
    ledger.tx_map_mut().clear_synching();

    assert!(!inbound.is_done());
    assert!(!inbound.revalidate_map_sync_with_family(&family));
    inbound.maybe_finish(&journal);

    assert!(inbound.is_complete());
    assert_eq!(
        inbound.completion_disposition(),
        Some(InboundLedgerCompletionDisposition::Complete(
            ledger::InboundLedgerReason::Generic
        ))
    );
    assert!(
        !inbound
            .ledger()
            .expect("completed inbound ledger should remain available")
            .is_immutable()
    );
    inbound
        .accept_completed_ledger()
        .expect("owner acceptance should finalize completion");
    assert!(
        inbound
            .ledger()
            .expect("completed inbound ledger should remain available")
            .is_immutable()
    );
}

#[test]
fn inbound_take_header_hash_mismatch_is_rejected_without_failing_owner() {
    let header = sample_header(601, sample_hash(0x41), sample_hash(0x42));
    let mut inbound = InboundLedgerLocal::new(sample_hash(0x99), 601);
    let mut store = RecordingInboundStore::default();
    let journal = RecordingJournal::default();

    let accepted = inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    );

    assert!(!accepted);
    assert!(!inbound.is_failed());
    assert!(!inbound.planner_state().have_header);
    assert!(inbound.ledger().is_none());
    assert_eq!(store.stored_headers.borrow().len(), 0);
}

#[test]
fn inbound_receive_state_root_packet_marks_completion_when_other_map_is_already_done() {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(Uint256::from_array([0x51; 32]), vec![1; 12]),
        0,
    );
    let header = sample_header(602, state_leaf.get_hash(), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-receive-state-root");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));

    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::StateNode,
        vec![InboundLedgerNodeData::new(
            Some(SHAMapNodeId::default().get_raw_string()),
            state_leaf
                .serialize_for_wire()
                .expect("leaf wire serialization should succeed"),
        )],
    );
    let mut san = SHAMapAddNode::default();
    inbound.receive_node_packet_with_family(
        &packet,
        &mut san,
        &mut store,
        &mut fetch_pack,
        &family,
        &journal,
    );

    assert!(san.is_useful());
    assert!(inbound.planner_state().have_state);
    assert!(inbound.planner_state().have_transactions);
    assert!(inbound.is_complete());
    assert_eq!(
        inbound.completion_disposition(),
        Some(InboundLedgerCompletionDisposition::Complete(
            ledger::InboundLedgerReason::Generic
        ))
    );
    assert!(
        !inbound
            .ledger()
            .expect("completed inbound ledger should remain available")
            .is_immutable()
    );
}

#[test]
fn inbound_packet_steps_preserve_full_packet_stats_and_timer_progress() {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(Uint256::from_array([0x53; 32]), vec![1; 12]),
        0,
    );
    let state_root = SHAMapTreeNode::new_inner(0);
    state_root.set_child_hash(3, state_leaf.get_hash());
    state_root.update_hash();
    let header = sample_header(603, state_root.get_hash(), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let root = InboundLedgerNodeData::new(
        Some(SHAMapNodeId::default().get_raw_string()),
        state_root
            .serialize_for_wire()
            .expect("state root wire serialization should succeed"),
    );
    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::StateNode,
        vec![root; INBOUND_LEDGER_MAX_PACKET_NODES_PER_STEP * 2 + 1],
    );
    let journal = RecordingJournal::default();
    let config = LedgerConfig::default();

    let family_progress = family("inbound-step-progress");
    let mut progress_inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut progress_store = RecordingInboundStore::default();
    let mut progress_fetch_pack = RecordingFetchPack::default();
    let header_packet = InboundLedgerPacket::new(
        InboundLedgerDataType::Base,
        vec![InboundLedgerNodeData::new(None, raw_header_bytes(&header))],
    );
    let header_step = progress_inbound
        .process_packet_step_with_family_and_config(
            &header_packet,
            0,
            INBOUND_LEDGER_MAX_PACKET_NODES_PER_STEP,
            &journal,
            &config,
            &mut progress_store,
            &mut progress_fetch_pack,
            &family_progress,
        )
        .expect("header step should be accepted");
    assert!(header_step.stats.is_useful());
    progress_inbound.record_packet_progress(header_step.stats);
    assert_eq!(
        progress_inbound.timeout_expired(),
        ledger::InboundLedgerTimerResult::Progress
    );

    let family_full = family("inbound-step-full");
    let mut full = InboundLedgerLocal::new(wanted_hash, 0);
    let mut full_store = RecordingInboundStore::default();
    let mut full_fetch_pack = RecordingFetchPack::default();
    assert!(full.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &config,
        &mut full_store,
        &journal,
    ));
    let full_stats = full
        .process_packet_with_family_and_config(
            &packet,
            &journal,
            &config,
            &mut full_store,
            &mut full_fetch_pack,
            &family_full,
        )
        .expect("full packet should be accepted");
    full.record_packet_stats_with_family_and_config(full_stats, &journal, &config, &family_full);

    let family_steps = family("inbound-step-bounded");
    let mut stepped = InboundLedgerLocal::new(wanted_hash, 0);
    let mut stepped_store = RecordingInboundStore::default();
    let mut stepped_fetch_pack = RecordingFetchPack::default();
    assert!(stepped.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &config,
        &mut stepped_store,
        &journal,
    ));

    let mut next_node = 0;
    let mut steps = 0;
    let mut accumulated = SHAMapAddNode::default();
    loop {
        let step = stepped
            .process_packet_step_with_family_and_config(
                &packet,
                next_node,
                INBOUND_LEDGER_MAX_PACKET_NODES_PER_STEP,
                &journal,
                &config,
                &mut stepped_store,
                &mut stepped_fetch_pack,
                &family_steps,
            )
            .expect("bounded packet step should be accepted");
        stepped.record_packet_progress(step.stats);
        accumulated += step.stats;
        steps += 1;
        if step.complete {
            break;
        }
        next_node = step.next_node;
    }
    stepped.record_packet_stats_with_family_and_config(
        accumulated,
        &journal,
        &config,
        &family_steps,
    );

    assert_eq!(steps, 3);
    assert_eq!(accumulated, full_stats);
    assert_eq!(stepped.stats(), full.stats());
    assert_eq!(
        stepped_store.stored_nodes.borrow().len(),
        full_store.stored_nodes.borrow().len()
    );
}

#[test]
fn inbound_packet_step_validates_the_original_packet_before_mutating() {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(Uint256::from_array([0x54; 32]), vec![1; 12]),
        0,
    );
    let header = sample_header(604, state_leaf.get_hash(), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let valid = InboundLedgerNodeData::new(
        Some(SHAMapNodeId::default().get_raw_string()),
        state_leaf
            .serialize_for_wire()
            .expect("state root wire serialization should succeed"),
    );
    let mut nodes = vec![valid; INBOUND_LEDGER_MAX_PACKET_NODES_PER_STEP];
    nodes.push(InboundLedgerNodeData::new(None, vec![1, 2, 3]));
    let packet = InboundLedgerPacket::new(InboundLedgerDataType::StateNode, nodes);
    let family = family("inbound-step-malformed");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));
    assert_eq!(
        inbound.process_packet_step_with_family_and_config(
            &packet,
            0,
            INBOUND_LEDGER_MAX_PACKET_NODES_PER_STEP,
            &journal,
            &LedgerConfig::default(),
            &mut store,
            &mut fetch_pack,
            &family,
        ),
        Err(InboundLedgerPacketError::MissingNodeId)
    );
    assert!(!inbound.planner_state().have_state);
    assert!(store.stored_nodes.borrow().is_empty());
}

#[test]
fn inbound_completion_without_fetch_backed_fee_settings_is_failed_not_full() {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(Uint256::from_array([0x52; 32]), vec![1; 12]),
        0,
    );
    let header = sample_header(
        XRP_LEDGER_EARLIEST_FEES,
        state_leaf.get_hash(),
        SHAMapHash::default(),
    );
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-missing-fees");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));
    inbound
        .ledger_mut()
        .expect("header load should create a ledger")
        .set_node_fetcher(Arc::new(
            |_hash| -> Option<SharedIntrusive<SHAMapTreeNode>> { None },
        ));

    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::StateNode,
        vec![InboundLedgerNodeData::new(
            Some(SHAMapNodeId::default().get_raw_string()),
            state_leaf
                .serialize_for_wire()
                .expect("leaf wire serialization should succeed"),
        )],
    );
    let mut san = SHAMapAddNode::default();
    inbound.receive_node_packet_with_family(
        &packet,
        &mut san,
        &mut store,
        &mut fetch_pack,
        &family,
        &journal,
    );

    assert!(san.is_useful());
    assert!(inbound.is_failed());
    assert!(!inbound.is_complete());
    assert_eq!(
        inbound.completion_disposition(),
        Some(InboundLedgerCompletionDisposition::Failed)
    );
    assert!(
        !inbound
            .ledger()
            .expect("failed inbound ledger should retain diagnostic ledger")
            .state_map()
            .is_full()
    );
}

#[test]
fn inbound_receive_known_tx_node_attaches_child() {
    let child = SHAMapTreeNode::new_inner(0);
    child.set_child_hash(4, sample_hash(0x77));
    child.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(0);
    root.set_child_hash(3, child.get_hash());
    root.update_hash();

    let header = sample_header(603, SHAMapHash::default(), root.get_hash());
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-receive-known-tx");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));

    let mut san = SHAMapAddNode::default();
    assert!(
        inbound.take_tx_root_node_with_family(
            &root
                .serialize_for_wire()
                .expect("root wire serialization should succeed"),
            &mut san,
            &mut store,
            &mut fetch_pack,
            &family,
        )
    );

    let node_id = SHAMapNodeId::default()
        .get_child_node_id(3)
        .expect("child node id should exist");
    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::TransactionNode,
        vec![InboundLedgerNodeData::new(
            Some(node_id.get_raw_string()),
            child
                .serialize_for_wire()
                .expect("child wire serialization should succeed"),
        )],
    );
    san.reset();
    inbound.receive_node_packet_with_family(
        &packet,
        &mut san,
        &mut store,
        &mut fetch_pack,
        &family,
        &journal,
    );

    assert!(san.is_useful());
    let ledger = inbound.ledger().expect("ledger should remain loaded");
    assert!(
        ledger
            .tx_map()
            .root()
            .get_child(3)
            .expect("known child should attach")
            .is_inner()
    );
}

#[test]
fn inbound_receive_state_node_rejects_empty_payload() {
    let header = sample_header(602, sample_hash(0x81), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-empty-state-payload");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));

    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::StateNode,
        vec![InboundLedgerNodeData::new(
            Some(SHAMapNodeId::default().get_raw_string()),
            Vec::new(),
        )],
    );
    let mut san = SHAMapAddNode::default();
    inbound.receive_node_packet_with_family(
        &packet,
        &mut san,
        &mut store,
        &mut fetch_pack,
        &family,
        &journal,
    );

    assert!(!san.is_good());
    assert!(
        journal
            .warns
            .borrow()
            .iter()
            .any(|message| message == "Received bad node data")
    );
}

#[test]
fn inbound_receive_state_node_marks_completion_without_reprocessing_non_synching_map() {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(Uint256::from_array([0x30; 32]), vec![7; 12]),
        0,
    );
    let state_root = SHAMapTreeNode::new_inner(0);
    state_root.set_child_hash(3, state_leaf.get_hash());
    state_root.update_hash();

    let header = sample_header(605, state_root.get_hash(), SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-receive-state-reactivate-synching");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();

    assert!(inbound.take_header_with_config_and_store(
        &raw_header_bytes(&header),
        &LedgerConfig::default(),
        &mut store,
        &journal,
    ));

    let mut san = SHAMapAddNode::default();
    assert!(
        inbound.take_as_root_node_with_family(
            &state_root
                .serialize_for_wire()
                .expect("root wire serialization should succeed"),
            &mut san,
            &mut store,
            &mut fetch_pack,
            &family,
        )
    );

    inbound
        .ledger_mut()
        .expect("ledger should be present")
        .state_map_mut()
        .clear_synching();
    assert_eq!(
        inbound
            .ledger()
            .expect("ledger should remain available")
            .state_map()
            .state(),
        SyncState::Modifying
    );

    let node_id = SHAMapNodeId::default()
        .get_child_node_id(3)
        .expect("child node id should exist");
    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::StateNode,
        vec![InboundLedgerNodeData::new(
            Some(node_id.get_raw_string()),
            state_leaf
                .serialize_for_wire()
                .expect("leaf wire serialization should succeed"),
        )],
    );
    san.reset();
    inbound.receive_node_packet_with_family(
        &packet,
        &mut san,
        &mut store,
        &mut fetch_pack,
        &family,
        &journal,
    );

    assert!(!san.is_useful());
    assert!(san.is_good());
    let ledger = inbound
        .ledger()
        .expect("ledger should remain loaded after packet ingest");
    assert!(inbound.planner_state().have_state);
    assert!(ledger.state_map().root().get_child(3).is_none());
}

#[test]
fn inbound_packet_wrapper_rejects_missing_node_ids_and_processes_base_slots() {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(Uint256::from_array([0x61; 32]), vec![2; 12]),
        0,
    );
    let tx_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionMd,
        SHAMapItem::new(Uint256::from_array([0x62; 32]), vec![3; 12]),
        0,
    );
    let header = sample_header(604, state_leaf.get_hash(), tx_leaf.get_hash());
    let wanted_hash = calculate_ledger_hash(&header);
    let family = family("inbound-process-base");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();

    let base = InboundLedgerPacket::new(
        InboundLedgerDataType::Base,
        vec![
            InboundLedgerNodeData::new(None, raw_header_bytes(&header)),
            InboundLedgerNodeData::new(
                None,
                state_leaf
                    .serialize_for_wire()
                    .expect("state root wire serialization should succeed"),
            ),
            InboundLedgerNodeData::new(
                None,
                tx_leaf
                    .serialize_for_wire()
                    .expect("tx root wire serialization should succeed"),
            ),
        ],
    );
    let san = inbound
        .process_packet_with_family_and_config(
            &base,
            &journal,
            &LedgerConfig::default(),
            &mut store,
            &mut fetch_pack,
            &family,
        )
        .expect("base packet should be accepted");

    assert_eq!(san.get_good(), 3);
    assert!(inbound.planner_state().have_header);
    assert_eq!(store.stored_headers.borrow().len(), 1);

    let invalid_nodes = InboundLedgerPacket::new(
        InboundLedgerDataType::StateNode,
        vec![InboundLedgerNodeData::new(None, vec![1, 2, 3])],
    );
    let error = inbound.process_packet_with_family_and_config(
        &invalid_nodes,
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );
    assert_eq!(error, Err(InboundLedgerPacketError::MissingNodeId));
}
