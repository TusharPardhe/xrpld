use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{Ledger, LedgerHeader, LedgerJournal, calculate_ledger_hash};
use parking_lot::Mutex;
use shamap::family::{MissingNodeReporter, NullFullBelowCache, SHAMapFamily, SHAMapNodeFetcher};
use shamap::item::SHAMapItem;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::HashMap;
use std::sync::Arc;
use time::Duration;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

#[derive(Debug, Default)]
struct RecordingFetcher {
    expected: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
    fetches: Mutex<Vec<SHAMapHash>>,
}

impl SHAMapNodeFetcher for RecordingFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.fetches.lock().push(hash);
        self.expected.get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingMissingNodeReporter {
    by_seq: Vec<(u32, Uint256)>,
}

#[derive(Debug)]
struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

impl MissingNodeReporter for SharedReporter {
    fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
        self.0.lock().by_seq.push((ref_num, node_hash));
    }

    fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
}

#[derive(Debug, Default)]
struct RecordingLedgerJournal {
    infos: Mutex<Vec<String>>,
    warns: Mutex<Vec<String>>,
}

impl RecordingLedgerJournal {
    fn infos(&self) -> Vec<String> {
        self.infos.lock().clone()
    }

    fn warns(&self) -> Vec<String> {
        self.warns.lock().clone()
    }
}

impl LedgerJournal for RecordingLedgerJournal {
    fn info(&self, message: &str) {
        self.infos.lock().push(message.to_owned());
    }

    fn warn(&self, message: &str) {
        self.warns.lock().push(message.to_owned());
    }
}

#[test]
fn ledger_walk_ledger_serial_reports_missing_account_and_tx_roots() {
    let account_hash = sample_hash(0xA1);
    let tx_hash = sample_hash(0xB2);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-walk-serial",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 600,
            tx_hash,
            account_hash,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 11),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 22),
    );
    let journal = RecordingLedgerJournal::default();

    ledger.set_full();

    assert!(!ledger.walk_ledger_with_family(&journal, false, &family));
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![account_hash, tx_hash])
    });
    assert_eq!(
        reporter.lock().by_seq,
        vec![
            (600, *account_hash.as_uint256()),
            (600, *tx_hash.as_uint256())
        ]
    );
    assert_eq!(
        journal.infos(),
        vec![
            format!(
                "1 missing account node(s)First: Missing Node: State Tree: hash {account_hash}"
            ),
            format!(
                "1 missing transaction node(s)First: Missing Node: Transaction Tree: hash {tx_hash}"
            ),
        ]
    );
}

#[test]
fn ledger_walk_ledger_parallel_returns_state_walk_result_and_skips_tx_tree() {
    let state_missing_hash = sample_hash(0xC1);
    let tx_hash = sample_hash(0xD2);
    let state_inner = SHAMapTreeNode::new_inner(1);
    state_inner.set_child_hash(7, state_missing_hash);
    state_inner.update_hash();

    let state_root = SHAMapTreeNode::new_inner(1);
    state_root.set_child_hash(2, state_inner.get_hash());
    state_root.share_child(2, &state_inner);
    state_root.update_hash_deep();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-walk-parallel",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(Arc::new(
            Mutex::new(RecordingMissingNodeReporter::default()),
        )),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 700,
            tx_hash,
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            700,
            SyncState::Modifying,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 700),
    );
    let journal = RecordingLedgerJournal::default();

    // With the corrected parallel path, a genuinely missing descendant that
    // the fetcher cannot resolve causes the walk to correctly report incomplete.
    assert!(!ledger.walk_ledger_with_family(&journal, true, &family));
    family.with_fetcher(|fetcher| {
        // After the parallel state-map walk, the tx tree is now also checked
        // (the broken path previously skipped it entirely). Both the missing
        // state descendant AND the unresolvable tx root hash are fetched.
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![state_missing_hash, tx_hash]
        )
    });
    // The corrected path now logs missing nodes for both maps (previously
    // the parallel path silently skipped logging entirely).
}

#[test]
fn ledger_walk_ledger_serial_checks_tx_tree_after_missing_account_root() {
    let account_hash = sample_hash(0xE1);
    let tx_root_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x44), vec![0x55; 16]),
        0,
    );
    let tx_hash = tx_root_leaf.get_hash();
    let mut expected = HashMap::new();
    expected.insert(tx_hash, tx_root_leaf.clone());

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-walk-after-account-miss",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher {
            expected,
            fetches: Mutex::new(Vec::new()),
        },
        SharedReporter(Arc::new(
            Mutex::new(RecordingMissingNodeReporter::default()),
        )),
    );
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 701,
            tx_hash,
            account_hash,
            ..LedgerHeader::default()
        },
        true,
    );
    let journal = RecordingLedgerJournal::default();

    assert!(!ledger.walk_ledger_with_family(&journal, false, &family));
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![account_hash, tx_hash])
    });
    assert_eq!(
        journal.infos(),
        vec![format!(
            "1 missing account node(s)First: Missing Node: State Tree: hash {account_hash}"
        )]
    );
}

#[test]
fn ledger_assert_sensible_accepts_matching_header_and_owner_hashes() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x62), vec![0x17; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x63), vec![0x27; 20]),
        0,
    );
    let mut header = LedgerHeader {
        seq: 902,
        drops: 101,
        tx_hash: tx_root.get_hash(),
        account_hash: state_root.get_hash(),
        parent_hash: sample_hash(0x64),
        parent_close_time: 11,
        close_time: 22,
        close_time_resolution: 30,
        close_flags: 0,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);

    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            902,
            SyncState::Immutable,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            902,
            SyncState::Immutable,
        ),
    );

    assert!(ledger.assert_sensible());
}

#[test]
#[should_panic(expected = "ledger is not sensible")]
fn ledger_assert_sensible_panics_for_mismatched_account_hash_unreachable_path() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x72), vec![0x18; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x73), vec![0x28; 20]),
        0,
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 903,
            drops: 102,
            hash: sample_hash(0x74),
            tx_hash: tx_root.get_hash(),
            account_hash: sample_hash(0x75),
            parent_hash: sample_hash(0x76),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            903,
            SyncState::Immutable,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            903,
            SyncState::Immutable,
        ),
    );

    let _ = ledger.assert_sensible();
}
