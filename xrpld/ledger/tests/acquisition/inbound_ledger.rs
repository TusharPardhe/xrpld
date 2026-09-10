use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    InboundLedgerObjectType, InboundLedgerPlannerState, Ledger, LedgerHeader,
    get_needed_hashes_with_family,
};
use shamap::family::{NullFullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily};
use shamap::fetch::SHAMapSyncFilter;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::SHAMapTreeNode;
use shamap::tree_node_cache::TreeNodeCache;
use std::sync::Arc;
use time::Duration;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
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

#[test]
fn inbound_get_needed_hashes_returns_ledger_hash_before_header() {
    let hash = sample_hash(0x11);
    let family = family("inbound-needed-header");
    let mut no_state_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut no_tx_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert_eq!(
        get_needed_hashes_with_family(
            hash,
            None,
            InboundLedgerPlannerState {
                have_header: false,
                have_state: false,
                have_transactions: false,
            },
            &mut no_state_filter,
            &mut no_tx_filter,
            &family,
        ),
        vec![(InboundLedgerObjectType::Ledger, *hash.as_uint256())]
    );
}

#[test]
fn inbound_needed_state_and_tx_hashes_return_roots_when_maps_are_empty() {
    let account_hash = sample_hash(0x21);
    let tx_hash = sample_hash(0x22);
    let family = family("inbound-needed-empty-roots");
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 90,
            account_hash,
            tx_hash,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 90),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 90),
    );
    let mut no_state_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut no_tx_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert_eq!(
        ledger.needed_state_hashes_with_family(4, &mut no_state_filter, &family),
        vec![*account_hash.as_uint256()]
    );
    assert_eq!(
        ledger.needed_tx_hashes_with_family(4, &mut no_tx_filter, &family),
        vec![*tx_hash.as_uint256()]
    );
}

#[test]
fn inbound_needed_hashes_return_missing_descendants_once_root_is_present() {
    let missing_state_hash = sample_hash(0x31);
    let state_root = SHAMapTreeNode::new_inner(1);
    state_root.set_child_hash(6, missing_state_hash);
    state_root.update_hash();

    let missing_tx_hash = sample_hash(0x41);
    let tx_root = SHAMapTreeNode::new_inner(1);
    tx_root.set_child_hash(9, missing_tx_hash);
    tx_root.update_hash();

    let family = family("inbound-needed-descendants");
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 91,
            account_hash: state_root.get_hash(),
            tx_hash: tx_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(state_root, SHAMapType::State, true, 91, SyncState::Synching),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            91,
            SyncState::Synching,
        ),
    );
    let mut no_state_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut no_tx_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert_eq!(
        ledger.needed_state_hashes_with_family(4, &mut no_state_filter, &family),
        vec![*missing_state_hash.as_uint256()]
    );
    assert_eq!(
        ledger.needed_tx_hashes_with_family(4, &mut no_tx_filter, &family),
        vec![*missing_tx_hash.as_uint256()]
    );
}

#[test]
fn inbound_get_needed_hashes_matches_current_cpp_hash_only_planner() {
    let account_hash = sample_hash(0x51);
    let tx_hash = sample_hash(0x52);
    let family = family("inbound-needed-planner");
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 92,
            account_hash,
            tx_hash,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 92),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 92),
    );
    let mut no_state_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut no_tx_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert_eq!(
        get_needed_hashes_with_family(
            sample_hash(0x99),
            Some(&mut ledger),
            InboundLedgerPlannerState {
                have_header: true,
                have_state: false,
                have_transactions: false,
            },
            &mut no_state_filter,
            &mut no_tx_filter,
            &family,
        ),
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
fn inbound_get_needed_hashes_skips_completed_maps() {
    let account_root = SHAMapTreeNode::new_inner(1);
    account_root.update_hash();
    let missing_tx_hash = sample_hash(0x61);
    let tx_root = SHAMapTreeNode::new_inner(1);
    tx_root.set_child_hash(3, missing_tx_hash);
    tx_root.update_hash();

    let family = family("inbound-needed-complete-state");
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 93,
            account_hash: account_root.get_hash(),
            tx_hash: tx_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            account_root,
            SHAMapType::State,
            true,
            93,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            93,
            SyncState::Synching,
        ),
    );
    let mut no_state_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut no_tx_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert_eq!(
        get_needed_hashes_with_family(
            sample_hash(0x98),
            Some(&mut ledger),
            InboundLedgerPlannerState {
                have_header: true,
                have_state: true,
                have_transactions: false,
            },
            &mut no_state_filter,
            &mut no_tx_filter,
            &family,
        ),
        vec![(
            InboundLedgerObjectType::TransactionNode,
            *missing_tx_hash.as_uint256()
        )]
    );
}
