use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    InboundLedgerJournal, InboundLedgerLocal, InboundLedgerStore, LedgerConfig, LedgerHeader,
    deserialize_prefixed_ledger_header, serialize_prefixed_ledger_header,
};
use parking_lot::Mutex;
use shamap::family::{
    NullFullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily, SHAMapNodeFetcher,
};
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

impl ledger::FetchPackContainer for RecordingFetchPack {
    fn get_fetch_pack(&mut self, hash: Uint256) -> Option<Blob> {
        self.blobs.borrow().get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingJournal {
    traces: RefCell<Vec<String>>,
    debugs: RefCell<Vec<String>>,
    warns: RefCell<Vec<String>>,
    fatals: RefCell<Vec<String>>,
}

impl InboundLedgerJournal for RecordingJournal {
    fn trace(&self, message: &str) {
        self.traces.borrow_mut().push(message.to_owned());
    }

    fn debug(&self, message: &str) {
        self.debugs.borrow_mut().push(message.to_owned());
    }

    fn warn(&self, message: &str) {
        self.warns.borrow_mut().push(message.to_owned());
    }

    fn fatal(&self, message: &str) {
        self.fatals.borrow_mut().push(message.to_owned());
    }
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

#[derive(Debug, Default)]
struct DelayedNodeFetcher {
    nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
    delayed_once: Mutex<HashMap<SHAMapHash, usize>>,
}

impl SHAMapNodeFetcher for DelayedNodeFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        if let Some(remaining_misses) = self.delayed_once.lock().get_mut(&hash) {
            if *remaining_misses > 0 {
                *remaining_misses -= 1;
                return None;
            }
        }
        self.nodes.get(&hash).cloned()
    }
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
fn ledger_header_prefixed_round_trip_matches_current_cpp_wire_shape() {
    let header = sample_header(500, sample_hash(0x11), sample_hash(0x12));
    let wire = serialize_prefixed_ledger_header(&header, false);
    let decoded = deserialize_prefixed_ledger_header(&wire, false)
        .expect("prefixed ledger header should deserialize");

    assert_eq!(decoded.seq, header.seq);
    assert_eq!(decoded.drops, header.drops);
    assert_eq!(decoded.parent_hash, header.parent_hash);
    assert_eq!(decoded.tx_hash, header.tx_hash);
    assert_eq!(decoded.account_hash, header.account_hash);
    assert_eq!(decoded.parent_close_time, header.parent_close_time);
    assert_eq!(decoded.close_time, header.close_time);
    assert_eq!(decoded.close_time_resolution, header.close_time_resolution);
    assert_eq!(decoded.close_flags, header.close_flags);
}

#[test]
fn inbound_try_db_prefers_local_header_source() {
    let account_hash = sample_hash(0x21);
    let header = sample_header(501, account_hash, SHAMapHash::default());
    let wanted_hash = ledger::calculate_ledger_hash(&header);
    let blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    store
        .headers
        .borrow_mut()
        .insert(*wanted_hash.as_uint256(), blob.clone());
    let mut fetch_pack = RecordingFetchPack::default();
    fetch_pack
        .blobs
        .borrow_mut()
        .insert(*wanted_hash.as_uint256(), vec![0xFF; blob.len()]);
    let family = family("inbound-trydb-local-header");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);

    inbound.try_db_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );

    assert!(inbound.ledger().is_some());
    assert!(inbound.planner_state().have_header);
    assert!(!inbound.planner_state().have_state);
    assert!(inbound.planner_state().have_transactions);
    assert!(!inbound.is_complete());
    assert!(!inbound.is_failed());
    assert_eq!(inbound.seq(), 501);
    assert_eq!(
        journal.traces.borrow().as_slice(),
        &[
            "Ledger header found in local store",
            "No TXNs to fetch",
            // Rust-side trace for the state-root fetch attempt (C++ does not emit this).
            &format!(
                "AS root check account_hash={} fetched=false map_hash_before={} map_hash_after={}",
                sample_hash(0x21),
                SHAMapHash::default(),
                SHAMapHash::default(),
            ),
        ]
    );
    assert!(store.stored_headers.borrow().is_empty());
}

#[test]
fn inbound_try_db_fetch_pack_path_completes_when_header_and_state_root_are_local() {
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
    let header = sample_header(502, state_root.get_hash(), SHAMapHash::default());
    let header_hash = ledger::calculate_ledger_hash(&header);
    let header_blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();
    fetch_pack
        .blobs
        .borrow_mut()
        .insert(*header_hash.as_uint256(), header_blob.clone());
    fetch_pack
        .blobs
        .borrow_mut()
        .insert(*state_root.get_hash().as_uint256(), state_blob.clone());
    let family = family("inbound-trydb-fetch-pack");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(header_hash, 0);

    inbound.try_db_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );

    assert!(inbound.is_complete());
    assert!(!inbound.is_failed());
    assert_eq!(
        inbound.planner_state(),
        ledger::InboundLedgerPlannerState {
            have_header: true,
            have_state: true,
            have_transactions: true,
        }
    );
    assert_eq!(
        inbound.completion_disposition(),
        Some(ledger::InboundLedgerCompletionDisposition::Complete(
            ledger::InboundLedgerReason::Generic
        ))
    );
    assert!(
        !inbound
            .ledger()
            .expect("completed inbound acquisition should hold a ledger")
            .is_immutable()
    );
    assert_eq!(store.stored_headers.borrow().len(), 1);
    assert_eq!(store.stored_nodes.borrow().len(), 1);
    assert_eq!(
        store.stored_nodes.borrow()[0].object_type(),
        NodeObjectType::AccountNode
    );
    assert_eq!(
        journal.traces.borrow().as_slice(),
        &[
            "Ledger header found in fetch pack",
            "No TXNs to fetch",
            // Rust-side trace for the state-root fetch attempt (C++ does not emit this).
            &format!(
                "AS root check account_hash={} fetched=true map_hash_before={} map_hash_after={}",
                state_root.get_hash(),
                SHAMapHash::default(),
                state_root.get_hash(),
            ),
            "Had full AS map locally",
        ]
    );
    assert_eq!(
        journal.debugs.borrow().as_slice(),
        &["Had everything locally"]
    );
}

#[test]
fn inbound_try_db_zero_account_hash_fails() {
    let header = sample_header(503, SHAMapHash::default(), SHAMapHash::default());
    let header_hash = ledger::calculate_ledger_hash(&header);
    let header_blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    let mut fetch_pack = RecordingFetchPack::default();
    fetch_pack
        .blobs
        .borrow_mut()
        .insert(*header_hash.as_uint256(), header_blob);
    let family = family("inbound-trydb-zero-account");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(header_hash, 0);

    inbound.try_db_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );

    assert!(inbound.is_failed());
    assert!(!inbound.is_complete());
    assert!(inbound.planner_state().have_header);
    assert!(inbound.planner_state().have_transactions);
    assert!(!inbound.planner_state().have_state);
    assert_eq!(
        journal.fatals.borrow().as_slice(),
        &["We are acquiring a ledger with a zero account hash"]
    );
}

#[test]
fn inbound_try_db_rejects_mismatched_header_identity() {
    let header = sample_header(505, sample_hash(0x31), SHAMapHash::default());
    let header_blob = serialize_prefixed_ledger_header(&header, false);
    let wanted_hash = sample_hash(0xAA);
    let mut store = RecordingInboundStore::default();
    store
        .headers
        .borrow_mut()
        .insert(*wanted_hash.as_uint256(), header_blob);
    let mut fetch_pack = RecordingFetchPack::default();
    let family = family("inbound-trydb-mismatch");
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(wanted_hash, 0);

    inbound.try_db_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );

    assert!(inbound.is_failed());
    assert!(!inbound.planner_state().have_header);
    assert!(inbound.ledger().is_none());
    assert_eq!(
        journal.warns.borrow().as_slice(),
        &[format!("hash {} seq 0 cannot be a ledger", wanted_hash)]
    );
}

#[test]
fn inbound_try_db_keeps_synching_when_get_missing_nodes_reports_missing_hash() {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        shamap::item::SHAMapItem::new(
            Uint256::from_array([0x61; 32]),
            vec![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 9, 8, 7, 6, 5, 4],
        ),
        0,
    );
    let state_root = SHAMapTreeNode::new_inner(1);
    state_root.set_child_hash(3, state_leaf.get_hash());
    state_root.update_hash();
    // Save the hash before state_root is moved into the fetcher.
    let state_root_hash = state_root.get_hash();

    let header = sample_header(506, state_root_hash, SHAMapHash::default());
    let header_hash = ledger::calculate_ledger_hash(&header);
    let header_blob = serialize_prefixed_ledger_header(&header, false);
    let mut store = RecordingInboundStore::default();
    store
        .headers
        .borrow_mut()
        .insert(*header_hash.as_uint256(), header_blob);
    let mut fetch_pack = RecordingFetchPack::default();
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "inbound-trydb-stale-synching",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(2),
        DelayedNodeFetcher {
            nodes: HashMap::from([
                (state_root.get_hash(), state_root),
                (state_leaf.get_hash(), state_leaf.clone()),
            ]),
            // The family scan performs an initial and a deferred completion
            // read before it records a missing child.
            delayed_once: Mutex::new(HashMap::from([(state_leaf.get_hash(), 2)])),
        },
        NullMissingNodeReporter,
    );
    let journal = RecordingJournal::default();
    let mut inbound = InboundLedgerLocal::new(header_hash, 0);

    inbound.try_db_with_family_and_config(
        &journal,
        &LedgerConfig::default(),
        &mut store,
        &mut fetch_pack,
        &family,
    );

    assert!(!inbound.is_complete());
    assert!(!inbound.is_failed());
    assert_eq!(
        inbound.planner_state(),
        ledger::InboundLedgerPlannerState {
            have_header: true,
            have_state: false,
            have_transactions: true,
        }
    );
    assert_eq!(
        journal.traces.borrow().as_slice(),
        &[
            "Ledger header found in local store",
            "No TXNs to fetch",
            // Rust-side trace for the state-root fetch attempt (C++ does not emit this).
            &format!(
                "AS root check account_hash={} fetched=true map_hash_before={} map_hash_after={}",
                state_root_hash,
                SHAMapHash::default(),
                state_root_hash,
            ),
        ]
    );
    assert!(journal.warns.borrow().is_empty());
    assert_eq!(journal.debugs.borrow().len(), 1);
    assert!(
        journal.debugs.borrow()[0].starts_with("AS map still missing hashes after local fetch")
    );
}
