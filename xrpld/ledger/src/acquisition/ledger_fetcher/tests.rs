use std::{
    collections::HashSet,
    sync::{
        Arc,
        atomic::{AtomicU32, Ordering},
    },
};

use basics::{base_uint::Uint256, sha_map_hash::SHAMapHash, tagged_cache::ManualClock};
use shamap::{
    family::{
        FullBelowCache, NullFullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily,
    },
    sync::{SHAMapType, SyncState},
    tree_node::SHAMapTreeNode,
    tree_node_cache::TreeNodeCache,
};
use time::Duration;

use super::{
    InboundLedgerDataType, InboundLedgerLocal, InboundLedgerNodeData, InboundLedgerPacket,
    InboundLedgerPacketShape, InboundLedgerPeerScore, InboundLedgerPlannerState, Ledger,
    NullInboundLedgerJournal, ProtocolPayload, SyncTree, TM_GET_OBJECT_BY_HASH_STATE_NODE,
    TreeKind, sample_peer_ids, sample_peer_ids_with,
};
use crate::LedgerHeader;
use protocol::XRP_LEDGER_EARLIEST_FEES;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn test_family(
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

#[derive(Clone)]
struct TrackingFullBelowCache {
    generation: Arc<AtomicU32>,
    clear_count: Arc<AtomicU32>,
}

impl TrackingFullBelowCache {
    fn new(generation: u32) -> Self {
        Self {
            generation: Arc::new(AtomicU32::new(generation)),
            clear_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn clear_count(&self) -> u32 {
        self.clear_count.load(Ordering::Relaxed)
    }
}

impl FullBelowCache for TrackingFullBelowCache {
    fn generation(&self) -> u32 {
        self.generation.load(Ordering::Relaxed)
    }

    fn touch_if_exists(&self, _hash: Uint256) -> bool {
        false
    }

    fn insert(&self, _hash: Uint256) {}

    fn clear(&self) {
        self.clear_count.fetch_add(1, Ordering::Relaxed);
        self.generation.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn sample_peer_ids_returns_all_candidates_when_limit_covers_them() {
    let scores = vec![
        InboundLedgerPeerScore {
            peer_id: 11,
            useful_count: 5,
        },
        InboundLedgerPeerScore {
            peer_id: 22,
            useful_count: 4,
        },
    ];

    assert_eq!(sample_peer_ids(&scores, 6), vec![11, 22]);
}

#[test]
fn sample_peer_ids_with_draws_unique_subset() {
    let scores = vec![
        InboundLedgerPeerScore {
            peer_id: 1,
            useful_count: 8,
        },
        InboundLedgerPeerScore {
            peer_id: 2,
            useful_count: 7,
        },
        InboundLedgerPeerScore {
            peer_id: 3,
            useful_count: 6,
        },
        InboundLedgerPeerScore {
            peer_id: 4,
            useful_count: 5,
        },
    ];
    let mut picks = [1usize, 1usize].into_iter();
    let sampled = sample_peer_ids_with(&scores, 2, &mut |_| {
        picks.next().expect("test picker should have enough draws")
    });

    assert_eq!(sampled.len(), 2);
    assert_eq!(sampled.iter().copied().collect::<HashSet<_>>().len(), 2);
    assert!(
        sampled
            .iter()
            .all(|peer_id| [1u64, 2, 3, 4].contains(peer_id))
    );
}

#[test]
fn packet_shape_skips_raw_base_header_and_classifies_bundled_roots() {
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(3, sample_hash(0x73));
    root.update_hash();
    let root_wire = root
        .serialize_for_wire()
        .expect("non-empty root should serialize for wire");
    assert!(
        SHAMapTreeNode::make_from_wire(&root_wire)
            .expect("root wire should decode")
            .expect("root wire should be non-empty")
            .is_inner()
    );

    // Base slot 0 is rippled's raw LedgerHeader serialization. Slots 1 and 2
    // are `serializeRoot` values, which rippled serializes with
    // `SHAMapTreeNode::serializeForWire`.
    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::Base,
        vec![
            InboundLedgerNodeData::new(None, vec![0xAB; 123]),
            InboundLedgerNodeData::new(None, root_wire),
        ],
    );

    let shape = InboundLedgerPacketShape::classify(&packet);
    assert_eq!(shape.nodes, 2);
    assert_eq!(shape.inner_nodes, 1);
    assert_eq!(shape.leaf_nodes, 0);
    assert_eq!(shape.empty_nodes, 0);
    assert_eq!(shape.malformed_nodes, 0);
}

#[test]
fn packet_shape_classifies_inner_empty_and_malformed_nodes() {
    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(3, sample_hash(0x33));
    inner.update_hash();
    let inner_wire = inner
        .serialize_for_wire()
        .expect("non-empty inner should serialize");

    let packet = InboundLedgerPacket::new(
        InboundLedgerDataType::StateNode,
        vec![
            InboundLedgerNodeData::new(Some(vec![0]), inner_wire),
            InboundLedgerNodeData::new(Some(vec![1]), Vec::new()),
            InboundLedgerNodeData::new(Some(vec![2]), vec![99]),
        ],
    );

    let shape = InboundLedgerPacketShape::classify(&packet);

    assert_eq!(shape.nodes, 3);
    assert_eq!(shape.inner_nodes, 1);
    assert_eq!(shape.leaf_nodes, 0);
    assert_eq!(shape.empty_nodes, 1);
    assert_eq!(shape.malformed_nodes, 1);
}

#[test]
fn complete_tree_plan_clears_only_the_completed_map_synching_state() {
    let state_root = SHAMapTreeNode::new_inner(0);
    state_root.update_hash();
    let tx_root = SHAMapTreeNode::new_inner(0);
    tx_root.update_hash();
    let mut inbound = InboundLedgerLocal::new(sample_hash(0x43), 77);
    inbound.ledger = Some(Ledger::from_maps(
        LedgerHeader {
            seq: 77,
            account_hash: state_root.get_hash(),
            tx_hash: tx_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(state_root, SHAMapType::State, true, 77, SyncState::Synching),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            77,
            SyncState::Synching,
        ),
    ));
    inbound.planner_state = InboundLedgerPlannerState {
        have_header: true,
        have_state: false,
        have_transactions: false,
    };

    assert!(inbound.complete_tree_plan(TreeKind::State));
    let ledger = inbound.ledger.as_ref().expect("ledger remains attached");
    assert!(!ledger.state_map().is_synching());
    assert!(ledger.tx_map().is_synching());
    assert!(!inbound.is_complete());

    assert!(inbound.complete_tree_plan(TreeKind::Transaction));
    let ledger = inbound.ledger.as_ref().expect("ledger remains attached");
    assert!(!ledger.tx_map().is_synching());
    assert!(inbound.is_complete());
}

#[test]
fn completion_reopen_requests_missing_state_hashes_by_hash() {
    let missing_state_hash = sample_hash(0x71);
    let state_root = SHAMapTreeNode::new_inner(1);
    state_root.set_child_hash(5, missing_state_hash);
    state_root.update_hash();

    let tx_root = SHAMapTreeNode::new_inner(0);
    tx_root.update_hash();

    let mut inbound = InboundLedgerLocal::new(sample_hash(0x99), 94);
    inbound.ledger = Some(Ledger::from_maps(
        LedgerHeader {
            seq: 94,
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            94,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            94,
            SyncState::Modifying,
        ),
    ));
    inbound.planner_state = InboundLedgerPlannerState {
        have_header: true,
        have_state: true,
        have_transactions: true,
    };
    inbound.complete = true;

    let request = inbound
        .reopen_if_maps_incomplete_with_family(&test_family("inbound-completion-reopen"))
        .expect("missing state hash should reopen completion");

    assert!(!inbound.complete);
    assert!(!inbound.planner_state.have_state);
    assert!(inbound.planner_state.have_transactions);
    assert!(
        inbound
            .ledger
            .as_ref()
            .expect("ledger should stay attached")
            .state_map()
            .is_synching()
    );

    match request.payload {
        ProtocolPayload::GetObjects(message) => {
            assert_eq!(message.r#type, TM_GET_OBJECT_BY_HASH_STATE_NODE);
            assert_eq!(message.objects.len(), 1);
            assert_eq!(
                message.objects[0]
                    .hash
                    .as_ref()
                    .expect("missing hash payload"),
                &missing_state_hash.as_uint256().data().to_vec()
            );
        }
        other => panic!("expected GetObjects recovery request, got {other:?}"),
    }
}

#[test]
fn completion_fee_settings_failure_preserves_shared_full_below_cache() {
    let cache = TrackingFullBelowCache::new(7);
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "inbound-fee-settings-clear",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        cache.clone(),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let state_root = SHAMapTreeNode::new_inner(0);
    state_root.update_hash();
    let tx_root = SHAMapTreeNode::new_inner(0);
    tx_root.update_hash();

    let mut inbound = InboundLedgerLocal::new(sample_hash(0x44), XRP_LEDGER_EARLIEST_FEES);
    inbound.ledger = Some(Ledger::from_maps(
        LedgerHeader {
            seq: XRP_LEDGER_EARLIEST_FEES,
            account_hash: state_root.get_hash(),
            tx_hash: tx_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            XRP_LEDGER_EARLIEST_FEES,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            XRP_LEDGER_EARLIEST_FEES,
            SyncState::Modifying,
        ),
    ));
    inbound.complete = true;

    inbound.finish_if_done_with_family_and_config(
        &NullInboundLedgerJournal,
        &crate::LedgerConfig::default(),
        &family,
    );

    assert!(inbound.failed);
    assert!(!inbound.complete);
    assert_eq!(cache.clear_count(), 0);
}
