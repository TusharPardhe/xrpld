use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{AccountStateSF, FetchPackContainer, LedgerSyncFilterStore, TransactionStateSF};
use shamap::family::{NullFullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily};
use shamap::fetch::SHAMapSyncFilter;
use shamap::item::SHAMapItem;
use shamap::storage::{NodeObjectType, NodeStoreSink, StoredNode};
use shamap::sync::{SHAMapType, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;
use time::Duration;

#[derive(Debug, Default)]
struct RecordingNodeStore {
    stored: Rc<RefCell<Vec<StoredNode>>>,
}

impl NodeStoreSink for RecordingNodeStore {
    fn store(&mut self, node: StoredNode) {
        self.stored.borrow_mut().push(node);
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
struct RecordingLedgerSyncStore {
    stored: Rc<RefCell<Vec<StoredNode>>>,
    blobs: Rc<RefCell<HashMap<Uint256, Blob>>>,
}

impl LedgerSyncFilterStore for RecordingLedgerSyncStore {
    fn store_shamap_node(
        &mut self,
        object_type: NodeObjectType,
        data: Blob,
        hash: Uint256,
        ledger_seq: u32,
    ) {
        self.stored
            .borrow_mut()
            .push(StoredNode::new(object_type, data, hash, ledger_seq));
    }

    fn fetch_node_data(&self, hash: Uint256) -> Option<Blob> {
        self.blobs.borrow().get(&hash).cloned()
    }
}

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn make_leaf(node_type: SHAMapNodeType, fill: u8) -> SharedIntrusive<SHAMapTreeNode> {
    SHAMapTreeNode::new_leaf(
        node_type,
        SHAMapItem::new(
            Uint256::from_array([fill; 32]),
            vec![
                fill,
                fill.wrapping_add(1),
                fill.wrapping_add(2),
                fill.wrapping_add(3),
                fill.wrapping_add(4),
                fill.wrapping_add(5),
                fill.wrapping_add(6),
                fill.wrapping_add(7),
                fill.wrapping_add(8),
                fill.wrapping_add(9),
                fill.wrapping_add(10),
                fill.wrapping_add(11),
            ],
        ),
        0,
    )
}

#[test]
fn account_state_sf_fetch_pack_and_store_roles() {
    let hash = sample_hash(0x11);
    let blob = vec![1_u8, 2, 3, 4];
    let stored = Rc::new(RefCell::new(Vec::new()));
    let node_store = RecordingNodeStore {
        stored: stored.clone(),
    };
    let fetch_pack = RecordingFetchPack {
        blobs: Rc::new(RefCell::new(HashMap::from([(
            *hash.as_uint256(),
            blob.clone(),
        )]))),
    };
    let mut filter = AccountStateSF::new(node_store, fetch_pack);

    assert_eq!(filter.get_node(hash), Some(blob.clone()));

    filter.got_node(true, hash, 91, blob.clone(), SHAMapNodeType::AccountState);

    let stored = stored.borrow();
    assert_eq!(stored.len(), 1);
    assert_eq!(stored[0].object_type(), NodeObjectType::AccountNode);
    assert_eq!(stored[0].hash(), hash.as_uint256());
    assert_eq!(stored[0].ledger_seq(), 91);
    assert_eq!(stored[0].data(), blob);
}

#[test]
fn account_state_sf_does_not_treat_local_db_as_filter_source() {
    let hash = sample_hash(0x19);
    let mut filter = AccountStateSF::new(
        RecordingLedgerSyncStore {
            blobs: Rc::new(RefCell::new(HashMap::from([(
                *hash.as_uint256(),
                vec![9_u8, 9, 9],
            )]))),
            ..Default::default()
        },
        RecordingFetchPack::default(),
    );

    assert_eq!(filter.get_node(hash), None);
}

#[test]
fn transaction_state_sf_store_role_and_rejects_transaction_nm() {
    let hash = sample_hash(0x22);
    let blob = vec![9_u8, 8, 7];
    let stored = Rc::new(RefCell::new(Vec::new()));
    let node_store = RecordingNodeStore {
        stored: stored.clone(),
    };
    let fetch_pack = RecordingFetchPack {
        blobs: Rc::new(RefCell::new(HashMap::from([(
            *hash.as_uint256(),
            blob.clone(),
        )]))),
    };
    let mut filter = TransactionStateSF::new(node_store, fetch_pack);

    assert_eq!(filter.get_node(hash), Some(blob.clone()));

    filter.got_node(
        false,
        hash,
        123,
        blob.clone(),
        SHAMapNodeType::TransactionMd,
    );
    let stored_ref = stored.borrow();
    assert_eq!(stored_ref.len(), 1);
    assert_eq!(stored_ref[0].object_type(), NodeObjectType::TransactionNode);
    assert_eq!(stored_ref[0].hash(), hash.as_uint256());
    assert_eq!(stored_ref[0].ledger_seq(), 123);
    assert_eq!(stored_ref[0].data(), blob);
    drop(stored_ref);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        filter.got_node(false, hash, 124, vec![1, 2], SHAMapNodeType::TransactionNm);
    }));
    assert!(
        result.is_err(),
        "TransactionStateSF should reject tnTRANSACTION_NM like the C++ assert"
    );
}

#[test]
fn transaction_state_sf_does_not_treat_local_db_as_filter_source() {
    let hash = sample_hash(0x2A);
    let mut filter = TransactionStateSF::new(
        RecordingLedgerSyncStore {
            blobs: Rc::new(RefCell::new(HashMap::from([(
                *hash.as_uint256(),
                vec![7_u8, 7, 7],
            )]))),
            ..Default::default()
        },
        RecordingFetchPack::default(),
    );

    assert_eq!(filter.get_node(hash), None);
}

#[test]
fn account_state_sf_supports_backed_fetch_root_with_current_shamap_seams() {
    let leaf = make_leaf(SHAMapNodeType::AccountState, 0x33);
    let leaf_blob = leaf
        .serialize_with_prefix()
        .expect("account-state leaf prefix serialization should succeed");
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-account-state-sf",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::new_with_type(SHAMapType::State, true, 400);
    let stored = Rc::new(RefCell::new(Vec::new()));
    let node_store = RecordingNodeStore {
        stored: stored.clone(),
    };
    let fetch_pack = RecordingFetchPack {
        blobs: Rc::new(RefCell::new(HashMap::from([(
            *leaf.get_hash().as_uint256(),
            leaf_blob,
        )]))),
    };
    let mut filter = AccountStateSF::new(node_store, fetch_pack);
    let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

    assert!(tree.fetch_root_with_family(leaf.get_hash(), &mut filter_ref, &family));
    assert_eq!(tree.root().get_hash(), leaf.get_hash());
    let stored = stored.borrow();
    assert_eq!(stored.len(), 1);
    assert_eq!(stored[0].object_type(), NodeObjectType::AccountNode);
    assert_eq!(stored[0].hash(), leaf.get_hash().as_uint256());
    assert_eq!(stored[0].ledger_seq(), 400);
}

#[test]
fn transaction_state_sf_supports_backed_fetch_root_with_current_shamap_seams() {
    let leaf = make_leaf(SHAMapNodeType::TransactionMd, 0x44);
    let leaf_blob = leaf
        .serialize_with_prefix()
        .expect("transaction-with-meta leaf prefix serialization should succeed");
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-transaction-state-sf",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::new_with_type(SHAMapType::Transaction, true, 401);
    let stored = Rc::new(RefCell::new(Vec::new()));
    let node_store = RecordingNodeStore {
        stored: stored.clone(),
    };
    let fetch_pack = RecordingFetchPack {
        blobs: Rc::new(RefCell::new(HashMap::from([(
            *leaf.get_hash().as_uint256(),
            leaf_blob,
        )]))),
    };
    let mut filter = TransactionStateSF::new(node_store, fetch_pack);
    let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

    assert!(tree.fetch_root_with_family(leaf.get_hash(), &mut filter_ref, &family));
    assert_eq!(tree.root().get_hash(), leaf.get_hash());
    let stored = stored.borrow();
    assert_eq!(stored.len(), 1);
    assert_eq!(stored[0].object_type(), NodeObjectType::TransactionNode);
    assert_eq!(stored[0].hash(), leaf.get_hash().as_uint256());
    assert_eq!(stored[0].ledger_seq(), 401);
}
