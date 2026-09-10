use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    FetchPackContainer, InboundLedgerCompletionDisposition, InboundLedgerJournal,
    InboundLedgerLocal, InboundLedgerObjectType, InboundLedgerReason, InboundLedgerRequestTrigger,
    InboundLedgerStore, LedgerConfig, LedgerHeader, calculate_ledger_hash,
    make_get_ledger_with_node_ids, make_inbound_get_ledger_request,
    make_inbound_needed_by_hash_request, serialize_prefixed_ledger_header,
};
use overlay::ProtocolPayload;
use protocol::JsonValue;
use shamap::family::{NullFullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily};
use shamap::storage::{NodeObjectType, StoredNode};
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

impl FetchPackContainer for RecordingFetchPack {
    fn get_fetch_pack(&mut self, hash: Uint256) -> Option<Blob> {
        self.blobs.borrow().get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingJournal;

impl InboundLedgerJournal for RecordingJournal {
    fn trace(&self, _message: &str) {}
    fn debug(&self, _message: &str) {}
    fn warn(&self, _message: &str) {}
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

#[test]
fn inbound_owner_update_only_sets_seq_when_unknown_and_touches_last_action() {
    let hash = sample_hash(0x11);
    let mut inbound = InboundLedgerLocal::new_with_reason(hash, 0, InboundLedgerReason::History);

    assert_eq!(inbound.reason(), InboundLedgerReason::History);
    assert_eq!(inbound.seq(), 0);
    assert_eq!(inbound.last_action(), Duration::ZERO);

    inbound.update(700, Duration::seconds(5));
    assert_eq!(inbound.seq(), 700);
    assert_eq!(inbound.last_action(), Duration::seconds(5));

    inbound.update(701, Duration::seconds(9));
    assert_eq!(inbound.seq(), 700);
    assert_eq!(inbound.last_action(), Duration::seconds(9));
}

#[test]
fn inbound_owner_check_local_returns_false_when_more_data_is_still_needed() {
    let account_hash = sample_hash(0x21);
    let header = sample_header(701, account_hash, SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    store
        .headers
        .borrow_mut()
        .insert(*wanted_hash.as_uint256(), blob);
    let family = family("inbound-owner-check-local-false");
    let journal = RecordingJournal;
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);

    assert!(!inbound.check_local_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut RecordingFetchPack::default(),
        &family,
    ));
    assert!(!inbound.is_done());
    assert!(inbound.planner_state().have_header);
    assert!(!inbound.planner_state().have_state);
}

#[test]
fn inbound_owner_check_local_returns_true_when_local_state_completes() {
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        shamap::item::SHAMapItem::new(
            Uint256::from_array([0x42; 32]),
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
        ),
        0,
    );
    let state_blob = state_root
        .serialize_with_prefix()
        .expect("state root prefix serialization should succeed");
    let header = sample_header(702, state_root.get_hash(), SHAMapHash::default());
    let header_hash = calculate_ledger_hash(&header);
    let header_blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();
    fetch_pack
        .blobs
        .borrow_mut()
        .insert(*header_hash.as_uint256(), header_blob);
    fetch_pack
        .blobs
        .borrow_mut()
        .insert(*state_root.get_hash().as_uint256(), state_blob);
    let family = family("inbound-owner-check-local-true");
    let journal = RecordingJournal;
    let mut inbound = InboundLedgerLocal::new(header_hash, 0);

    assert!(inbound.check_local_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    ));
    assert!(inbound.is_complete());
    assert_eq!(
        inbound.completion_disposition(),
        Some(InboundLedgerCompletionDisposition::Complete(
            InboundLedgerReason::Generic
        ))
    );
    let ledger = inbound
        .ledger()
        .expect("completed inbound owner should hold a ledger");
    assert!(!ledger.is_immutable());
    assert!(!ledger.state_map().is_full());
    assert!(!ledger.tx_map().is_full());
    assert_eq!(
        inbound.accept_completed_ledger(),
        Some(InboundLedgerCompletionDisposition::Complete(
            InboundLedgerReason::Generic
        ))
    );
    assert!(
        inbound
            .ledger()
            .expect("completed inbound owner should hold a ledger")
            .is_immutable()
    );
}

#[test]
fn inbound_owner_completion_reports_reason_before_owner_acceptance() {
    for reason in [InboundLedgerReason::History, InboundLedgerReason::Consensus] {
        let state_root = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            shamap::item::SHAMapItem::new(
                Uint256::from_array([0x43; 32]),
                vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
            ),
            0,
        );
        let state_blob = state_root
            .serialize_with_prefix()
            .expect("state root prefix serialization should succeed");
        let header = sample_header(703, state_root.get_hash(), SHAMapHash::default());
        let header_hash = calculate_ledger_hash(&header);
        let header_blob = serialize_prefixed_ledger_header(&header, false);
        let mut store = RecordingInboundStore::default();
        let mut fetch_pack = RecordingFetchPack::default();
        fetch_pack
            .blobs
            .borrow_mut()
            .insert(*header_hash.as_uint256(), header_blob);
        fetch_pack
            .blobs
            .borrow_mut()
            .insert(*state_root.get_hash().as_uint256(), state_blob);
        let family = family("inbound-owner-completion-reason");
        let journal = RecordingJournal;
        let mut inbound = InboundLedgerLocal::new_with_reason(header_hash, 0, reason);

        assert!(inbound.check_local_with_family_and_config(
            &journal,
            &LedgerConfig::default(),
            &mut store,
            &mut fetch_pack,
            &family,
        ));
        assert_eq!(
            inbound.completion_disposition(),
            Some(InboundLedgerCompletionDisposition::Complete(reason))
        );
        assert!(
            !inbound
                .ledger()
                .expect("completed inbound owner should hold a ledger")
                .is_immutable()
        );
    }
}

#[test]
fn inbound_owner_get_needed_hashes_returns_typed_requests() {
    let account_hash = sample_hash(0x31);
    let tx_hash = sample_hash(0x32);
    let header = sample_header(703, account_hash, tx_hash);
    let wanted_hash = calculate_ledger_hash(&header);
    let blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    store
        .headers
        .borrow_mut()
        .insert(*wanted_hash.as_uint256(), blob);
    let family = family("inbound-owner-needed-hashes");
    let journal = RecordingJournal;
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    inbound.check_local_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut RecordingFetchPack::default(),
        &family,
    );

    let mut state_filter = None;
    let mut tx_filter = None;
    assert_eq!(
        inbound.get_needed_hashes_with_family(&mut state_filter, &mut tx_filter, &family),
        vec![
            (
                InboundLedgerObjectType::StateNode,
                *account_hash.as_uint256()
            ),
            (
                InboundLedgerObjectType::TransactionNode,
                *tx_hash.as_uint256()
            ),
        ]
    );
}

#[test]
fn inbound_owner_by_hash_request_uses_first_needed_type_only() {
    let request = make_inbound_needed_by_hash_request(
        sample_hash(0x81),
        900,
        &[
            (
                InboundLedgerObjectType::StateNode,
                Uint256::from_array([0x11; 32]),
            ),
            (
                InboundLedgerObjectType::StateNode,
                Uint256::from_array([0x12; 32]),
            ),
            (
                InboundLedgerObjectType::TransactionNode,
                Uint256::from_array([0x13; 32]),
            ),
        ],
    )
    .expect("request should be built");

    match request.payload {
        ProtocolPayload::GetObjects(message) => {
            assert_eq!(message.r#type, 4);
            assert!(message.query);
            assert_eq!(
                message.ledger_hash,
                Some(sample_hash(0x81).as_uint256().data().to_vec())
            );
            assert_eq!(message.objects.len(), 2);
            assert_eq!(message.objects[0].ledger_seq, Some(900));
            assert_eq!(
                message.objects[0].hash,
                Some(Uint256::from_array([0x11; 32]).data().to_vec())
            );
            assert_eq!(
                message.objects[1].hash,
                Some(Uint256::from_array([0x12; 32]).data().to_vec())
            );
        }
        payload => panic!("expected get_objects payload, got {payload:?}"),
    }
}

#[test]
fn shared_base_request_omits_query_depth_for_rippled_peer_compatibility() {
    let request = make_get_ledger_with_node_ids(sample_hash(0x80), 900, 0, &[], 0, None);

    match request.payload {
        ProtocolPayload::GetLedger(message) => {
            assert_eq!(message.itype, 0);
            assert_eq!(message.ledger_seq, Some(900));
            assert_eq!(message.query_depth, None);
        }
        payload => panic!("expected get_ledger payload, got {payload:?}"),
    }
}

#[test]
fn inbound_owner_header_request_keeps_base_query_depth_unset() {
    let request = make_inbound_get_ledger_request(
        sample_hash(0x82),
        901,
        ledger::InboundLedgerDataType::Base,
        2,
        InboundLedgerRequestTrigger::Blind,
    );

    match request.payload {
        ProtocolPayload::GetLedger(message) => {
            assert_eq!(message.itype, 0);
            assert_eq!(message.ledger_seq, Some(901));
            // C++ always sets ledgerhash for all request types.
            assert_eq!(
                message.ledger_hash,
                Some(sample_hash(0x82).as_uint256().data().to_vec())
            );
            assert_eq!(message.query_type, None);
            assert_eq!(message.query_depth, None);
        }
        payload => panic!("expected get_ledger payload, got {payload:?}"),
    }
}

#[test]
fn inbound_owner_live_header_request_asks_by_sequence() {
    let inbound = InboundLedgerLocal::new(sample_hash(0x83), 902);
    let request = inbound.make_header_request();

    match request.payload {
        ProtocolPayload::GetLedger(message) => {
            assert_eq!(message.itype, 0);
            // C++ always sets ledgerhash for all request types.
            assert_eq!(
                message.ledger_hash,
                Some(sample_hash(0x83).as_uint256().data().to_vec())
            );
            assert_eq!(message.ledger_seq, Some(902));
            assert_eq!(message.query_type, None);
            assert_eq!(message.query_depth, None);
        }
        payload => panic!("expected get_ledger payload, got {payload:?}"),
    }
}

#[test]
fn inbound_owner_state_root_request_precedes_transaction_work() {
    let account_hash = sample_hash(0x84);
    let tx_hash = sample_hash(0x85);
    let header = sample_header(903, account_hash, tx_hash);
    let wanted_hash = calculate_ledger_hash(&header);
    let mut store = RecordingInboundStore::default();
    store.headers.borrow_mut().insert(
        *wanted_hash.as_uint256(),
        serialize_prefixed_ledger_header(&header, false),
    );
    let mut fetch_pack = RecordingFetchPack::default();
    let family = family("inbound-owner-state-first");
    let journal = RecordingJournal;
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);

    let setup = inbound.prepare_trigger(
        InboundLedgerRequestTrigger::Reply,
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );

    assert!(setup.state_request_pending);
    assert!(!setup.state_plan);
    assert!(!setup.tx_plan);
    assert_eq!(setup.messages_to_send.len(), 1);
    match &setup.messages_to_send[0].payload {
        ProtocolPayload::GetLedger(message) => {
            assert_eq!(message.itype, 2, "state root must be requested first");
            assert_eq!(message.query_depth, Some(1));
            assert_eq!(message.ledger_seq, Some(903));
        }
        payload => panic!("expected state-node GetLedger request, got {payload:?}"),
    }
}

#[test]
fn inbound_owner_get_info_reports_local_needed_hashes_subset() {
    let account_hash = sample_hash(0x41);
    let header = sample_header(704, account_hash, SHAMapHash::default());
    let wanted_hash = calculate_ledger_hash(&header);
    let blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    store
        .headers
        .borrow_mut()
        .insert(*wanted_hash.as_uint256(), blob);
    let family = family("inbound-owner-info");
    let journal = RecordingJournal;
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);
    inbound.check_local_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut RecordingFetchPack::default(),
        &family,
    );

    let JsonValue::Object(info) = inbound.get_info_with_family(&family) else {
        panic!("owner info should be a JSON object");
    };
    assert_eq!(
        info.get("hash"),
        Some(&JsonValue::String(wanted_hash.to_string()))
    );
    assert_eq!(info.get("have_header"), Some(&JsonValue::Bool(true)));
    assert_eq!(info.get("have_state"), Some(&JsonValue::Bool(false)));
    assert_eq!(info.get("have_transactions"), Some(&JsonValue::Bool(true)));
    assert_eq!(
        info.get("needed_state_hashes"),
        Some(&JsonValue::Array(vec![JsonValue::String(
            account_hash.to_string()
        )]))
    );
    assert!(!info.contains_key("needed_transaction_hashes"));
}
