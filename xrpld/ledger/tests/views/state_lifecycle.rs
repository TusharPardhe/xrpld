use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use ledger::{
    ApplyView, Fees, FlowSandbox, Ledger, LedgerHeader, OpenView, ReadView, SLCF_NO_CONSENSUS_TIME,
    Sandbox, adjust_owner_count, amendments_key, calculate_ledger_hash, dir_append, dir_insert,
    encode_amendments_entry, encode_fee_settings_entry, fees_key,
};
use protocol::{
    AccountID, ApplyFlags, IOUAmount, Issue, LedgerEntryType, STAmount, STLedgerEntry, Ter,
    XRPAmount, account_keylet, currency_from_string, directory_node_keylet, feature_xrp_fees,
    get_field_by_symbol, line, offer_keylet, owner_dir_keylet, page_keylet, sf_generic,
};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use std::sync::Arc;

#[test]
fn flow_sandbox_explicit_flags_override_parent_flags() {
    let base = std::sync::Arc::new(Ledger::new(LedgerHeader::default(), false));
    let mut parent = Sandbox::new(base, ApplyFlags::NONE);
    let retry_attempt = FlowSandbox::new_with_flags(&mut parent, ApplyFlags::RETRY);

    assert_eq!(retry_attempt.flags(), ApplyFlags::RETRY);
}

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

fn account(fill: u8) -> AccountID {
    AccountID::from_array([fill; 20])
}

fn build_state_map_with_items(items: &[(Uint256, Vec<u8>)], ledger_seq: u32) -> SyncTree {
    let mut tree = MutableTree::new(ledger_seq);
    for (key, payload) in items {
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(*key, payload.clone()),
        )
        .expect("state map item insertion should succeed");
    }

    SyncTree::from_root_with_type(
        tree.root(),
        SHAMapType::State,
        true,
        ledger_seq,
        SyncState::Modifying,
    )
}

#[test]
fn sandbox_apply_with_tx_thread_updates_threaded_sles() {
    let ledger_seq = 17254325;
    let account = account(0x33);
    let account_keylet = account_keylet(
        basics::base_uint::Uint160::from_slice(account.data()).expect("account width"),
    );
    let previous_tx = sample_uint256(0xA1);
    let current_tx = sample_uint256(0xB2);

    let mut account_root = STLedgerEntry::new(account_keylet);
    account_root.set_account_id(get_field_by_symbol("sfAccount"), account);
    account_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(1_000)),
    );
    account_root.set_field_u32(get_field_by_symbol("sfSequence"), 10);
    account_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    account_root.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), previous_tx);
    account_root.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), ledger_seq - 1);

    let state_map = build_state_map_with_items(
        &[(
            account_keylet.key,
            account_root.get_serializer().data().to_vec(),
        )],
        ledger_seq,
    );
    let base = Ledger::from_maps(
        LedgerHeader {
            seq: ledger_seq,
            ..LedgerHeader::default()
        },
        state_map.clone(),
        SyncTree::from_root_with_type(
            SHAMapTreeNode::new_inner(0),
            SHAMapType::Transaction,
            true,
            ledger_seq,
            SyncState::Modifying,
        ),
    );
    let rules = base.rules().clone();
    let mut parent = Sandbox::new(std::sync::Arc::new(base), protocol::ApplyFlags::default());
    let mut flow = FlowSandbox::new_with_flags(&mut parent, protocol::ApplyFlags::default());
    let checked_out = flow
        .peek(account_keylet)
        .expect("peek should succeed")
        .expect("account exists");
    let mut modified = checked_out.clone_as_object();
    modified.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(900)),
    );
    flow.update(std::sync::Arc::new(STLedgerEntry::from_stobject(
        modified,
        account_keylet.key,
    )))
    .expect("update should succeed");

    flow.apply_with_tx_thread(current_tx, ledger_seq, &rules)
        .expect("threaded flow apply should succeed");

    let threaded = parent
        .read(account_keylet)
        .expect("read should succeed")
        .expect("account remains");
    assert_eq!(
        threaded.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
        current_tx
    );
    assert_eq!(
        threaded.get_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq")),
        ledger_seq
    );
    assert_eq!(
        threaded
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        900
    );
}

#[test]
fn erased_ripple_state_threads_untouched_owners_after_nested_flow_sandbox() {
    let ledger_seq = 106_053_457;
    let low = account(0x44);
    let high = account(0x55);
    let low_keylet = account_keylet(
        basics::base_uint::Uint160::from_slice(low.data()).expect("low account width"),
    );
    let high_keylet = account_keylet(
        basics::base_uint::Uint160::from_slice(high.data()).expect("high account width"),
    );
    let currency = currency_from_string("USD");
    let ripple_state_keylet = line(low, high, currency);
    let previous_low_tx = sample_uint256(0xA1);
    let previous_high_tx = sample_uint256(0xA2);
    let current_tx = sample_uint256(0xB2);

    let account_root =
        |owner: AccountID, keylet: protocol::Keylet, balance, sequence, previous_tx| {
            let mut root =
                STLedgerEntry::from_type_and_key(LedgerEntryType::AccountRoot, keylet.key);
            root.set_account_id(get_field_by_symbol("sfAccount"), owner);
            root.set_field_amount(
                get_field_by_symbol("sfBalance"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(balance)),
            );
            root.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
            root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 7);
            root.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), previous_tx);
            root.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), ledger_seq - 1);
            root
        };
    let low_root = account_root(low, low_keylet, 1_000, 10, previous_low_tx);
    let high_root = account_root(high, high_keylet, 2_000, 20, previous_high_tx);

    let iou = |value, issuer| {
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(value, 0).expect("canonical IOU amount"),
            Issue::new(currency, issuer),
        )
    };
    let mut ripple_state =
        STLedgerEntry::from_type_and_key(LedgerEntryType::RippleState, ripple_state_keylet.key);
    ripple_state.set_field_amount(get_field_by_symbol("sfBalance"), iou(0, low));
    ripple_state.set_field_amount(get_field_by_symbol("sfLowLimit"), iou(100, low));
    ripple_state.set_field_amount(get_field_by_symbol("sfHighLimit"), iou(200, high));
    ripple_state.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xA3));
    ripple_state.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), ledger_seq - 1);

    let state_map = build_state_map_with_items(
        &[
            (low_keylet.key, low_root.get_serializer().data().to_vec()),
            (high_keylet.key, high_root.get_serializer().data().to_vec()),
            (
                ripple_state_keylet.key,
                ripple_state.get_serializer().data().to_vec(),
            ),
        ],
        // Keep fixture COW ownership below Ledger's mutable-tree allocation,
        // while the LedgerHeader below retains the transaction ledger sequence.
        1,
    );
    let base = Ledger::from_maps(
        LedgerHeader {
            seq: ledger_seq,
            ..LedgerHeader::default()
        },
        state_map.clone(),
        SyncTree::new_with_type(SHAMapType::Transaction, true, ledger_seq),
    );
    let mut built = Ledger::from_maps(
        base.header(),
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, true, ledger_seq),
    );

    let mut sandbox = Sandbox::new(Arc::new(base), ApplyFlags::NONE);
    {
        let mut flow = FlowSandbox::new(&mut sandbox);
        let line = flow
            .peek(ripple_state_keylet)
            .expect("peek RippleState")
            .expect("RippleState exists");
        flow.erase(line).expect("erase RippleState in flow sandbox");
        flow.apply()
            .expect("propagate RippleState erase to parent sandbox");
    }

    let rules = built.rules().clone();
    sandbox
        .apply_with_tx_thread(&mut built, current_tx, ledger_seq, &rules)
        .expect("commit threaded RippleState deletion");

    assert!(
        built
            .read(ripple_state_keylet)
            .expect("read deleted RippleState")
            .is_none()
    );
    for (keylet, balance, sequence) in [(low_keylet, 1_000, 10), (high_keylet, 2_000, 20)] {
        let owner = built
            .read(keylet)
            .expect("read threaded owner")
            .expect("owner AccountRoot remains");
        assert_eq!(
            owner.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
            current_tx
        );
        assert_eq!(
            owner.get_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq")),
            ledger_seq
        );
        assert_eq!(
            owner
                .get_field_amount(get_field_by_symbol("sfBalance"))
                .xrp()
                .drops(),
            balance,
            "owner business balance must remain unchanged"
        );
        assert_eq!(
            owner.get_field_u32(get_field_by_symbol("sfSequence")),
            sequence,
            "owner business sequence must remain unchanged"
        );
        assert_eq!(
            owner.get_field_u32(get_field_by_symbol("sfOwnerCount")),
            7,
            "owner business owner count must remain unchanged"
        );
    }
}

#[test]
fn same_ledger_offer_sequence_cancel_sees_committed_owner_directory_page() {
    let ledger_seq = 106_053_457;
    let owner = account(0x44);
    let owner_id = basics::base_uint::Uint160::from_slice(owner.data()).expect("account width");
    let account_keylet = account_keylet(owner_id);
    let owner_dir = owner_dir_keylet(owner_id);
    let offer_a_keylet = offer_keylet(owner_id, 765);
    let successor_offer_keylet = offer_keylet(owner_id, 766);
    let book_directory = Uint256::from_array([0xB7; 32]);
    let book_dir = directory_node_keylet(book_directory);

    let mut account_root =
        STLedgerEntry::from_type_and_key(LedgerEntryType::AccountRoot, account_keylet.key);
    account_root.set_account_id(get_field_by_symbol("sfAccount"), owner);
    account_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(10_000_000_000)),
    );
    account_root.set_field_u32(get_field_by_symbol("sfSequence"), 765);
    account_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);

    let state_map = build_state_map_with_items(
        &[(
            account_keylet.key,
            account_root.get_serializer().data().to_vec(),
        )],
        // An acquired ledger root is shareable (cowid 0). Use a smaller
        // fixture COW id than Ledger's first global mutable-tree id so this
        // test exercises directory propagation rather than fixture setup.
        1,
    );
    let mut built = Ledger::from_maps(
        LedgerHeader {
            seq: ledger_seq,
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, false, ledger_seq),
    );

    // Fill the owner root before the transaction so OfferCreate A must land on
    // page 1, matching the production failure where that page was lost between
    // two transactions in ledger 106053457.
    let mut seed = Sandbox::new(Arc::new(built.clone()), ApplyFlags::NONE);
    for key in (1..=32).map(Uint256::from_u64) {
        assert_eq!(
            dir_insert(&mut seed, &owner_dir, key, &|_| {}).expect("seed owner directory"),
            Some(0)
        );
    }
    seed.apply(&mut built)
        .expect("commit seeded owner directory");

    // Accepted-ledger construction accumulates each transaction in OpenView;
    // every subsequent transaction receives a clone of this live accumulator.
    let mut accumulated = OpenView::new_closed(Arc::new(built.clone()));

    // Transaction A: create an offer through the same nested FlowSandbox that
    // the transaction shell uses, then commit its sandbox to the built ledger.
    let mut create_tx = Sandbox::new(Arc::new(accumulated.clone()), ApplyFlags::NONE);
    {
        let mut tx_view = FlowSandbox::new(&mut create_tx);
        let owner_page = dir_insert(&mut tx_view, &owner_dir, offer_a_keylet.key, &|_| {})
            .expect("insert offer into owner directory")
            .expect("owner directory has another page");
        assert_eq!(owner_page, 1);
        let book_page = dir_append(&mut tx_view, &book_dir, offer_a_keylet.key, &|_| {})
            .expect("insert offer into book directory")
            .expect("book directory has a page");

        let mut offer =
            STLedgerEntry::from_type_and_key(LedgerEntryType::Offer, offer_a_keylet.key);
        offer.set_account_id(get_field_by_symbol("sfAccount"), owner);
        offer.set_field_h256(get_field_by_symbol("sfBookDirectory"), book_directory);
        offer.set_field_u64(get_field_by_symbol("sfOwnerNode"), owner_page);
        offer.set_field_u64(get_field_by_symbol("sfBookNode"), book_page);
        tx_view.insert(Arc::new(offer)).expect("insert offer SLE");
        let account = tx_view
            .peek(account_keylet)
            .expect("read owner account")
            .expect("owner account exists");
        adjust_owner_count(&mut tx_view, &account, 1).expect("increment owner count");
        tx_view.apply().expect("apply transaction sandbox");
    }
    let rules = built.rules().clone();
    create_tx
        .apply_with_tx_thread(
            &mut accumulated,
            Uint256::from_array([0x76; 32]),
            ledger_seq,
            &rules,
        )
        .expect("commit offer transaction");

    let owner_page_keylet = page_keylet(owner_dir, 1);
    let owner_root_after_create = accumulated
        .read(owner_dir)
        .expect("read committed owner root")
        .expect("owner root must propagate to the next transaction");
    assert_eq!(
        owner_root_after_create.get_field_u64(get_field_by_symbol("sfIndexNext")),
        1,
        "the root forward link must retain canonical owner page 1"
    );
    assert_eq!(
        owner_root_after_create.get_field_u64(get_field_by_symbol("sfIndexPrevious")),
        1,
        "the root backward link must retain canonical owner page 1"
    );
    let page_after_create = accumulated
        .read(owner_page_keylet)
        .expect("read committed owner page")
        .expect("owner page 1 must propagate to the next transaction");
    assert!(
        page_after_create
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value()
            .contains(&offer_a_keylet.key),
        "the committed owner page must contain OfferCreate A before OfferSequence cancellation"
    );

    // Transaction B creates the successor offer in the same ledger and on the
    // same owner-directory page. It must observe A's committed page entry
    // instead of recreating page 1 from a stale transaction base.
    let mut successor_tx = Sandbox::new(Arc::new(accumulated.clone()), ApplyFlags::NONE);
    {
        let mut tx_view = FlowSandbox::new(&mut successor_tx);
        let owner_page = dir_insert(
            &mut tx_view,
            &owner_dir,
            successor_offer_keylet.key,
            &|_| {},
        )
        .expect("insert successor offer into owner directory")
        .expect("owner directory page exists");
        assert_eq!(owner_page, 1);
        let book_page = dir_append(&mut tx_view, &book_dir, successor_offer_keylet.key, &|_| {})
            .expect("insert successor offer into book directory")
            .expect("book directory has a page");

        let mut offer =
            STLedgerEntry::from_type_and_key(LedgerEntryType::Offer, successor_offer_keylet.key);
        offer.set_account_id(get_field_by_symbol("sfAccount"), owner);
        offer.set_field_h256(get_field_by_symbol("sfBookDirectory"), book_directory);
        offer.set_field_u64(get_field_by_symbol("sfOwnerNode"), owner_page);
        offer.set_field_u64(get_field_by_symbol("sfBookNode"), book_page);
        tx_view
            .insert(Arc::new(offer))
            .expect("insert successor offer SLE");
        let account = tx_view
            .peek(account_keylet)
            .expect("read owner account")
            .expect("owner account exists");
        adjust_owner_count(&mut tx_view, &account, 1).expect("increment owner count");
        tx_view
            .apply()
            .expect("apply successor transaction sandbox");
    }
    let rules = built.rules().clone();
    successor_tx
        .apply_with_tx_thread(
            &mut accumulated,
            Uint256::from_array([0x78; 32]),
            ledger_seq,
            &rules,
        )
        .expect("commit successor offer transaction");
    let page_after_successor = accumulated
        .read(owner_page_keylet)
        .expect("read owner page after successor")
        .expect("owner page 1 must persist after successor offer");
    let successor_indexes = page_after_successor.get_field_v256(get_field_by_symbol("sfIndexes"));
    assert!(successor_indexes.value().contains(&offer_a_keylet.key));
    assert!(
        successor_indexes
            .value()
            .contains(&successor_offer_keylet.key)
    );

    // Transaction C: resolve A exactly as OfferSequence cancellation does,
    // then use the production offer_delete helper for directory cleanup.
    let mut cancel_tx = Sandbox::new(Arc::new(accumulated.clone()), ApplyFlags::NONE);
    let offer_a = cancel_tx
        .peek(offer_a_keylet)
        .expect("resolve OfferSequence target")
        .expect("OfferCreate A must be visible in the next transaction");
    let page_before_cancel = cancel_tx
        .read(owner_page_keylet)
        .expect("read owner page before cancel")
        .expect("owner page must be visible before cancel");
    assert!(
        page_before_cancel
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value()
            .contains(&offer_a_keylet.key)
    );
    assert_eq!(
        ledger::offer_helpers::offer_delete(&mut cancel_tx, offer_a).expect("delete offer"),
        Ter::TES_SUCCESS,
        "owner-directory removal must not be weakened into a tefBAD_LEDGER bypass"
    );
    assert_eq!(
        cancel_tx
            .read(account_keylet)
            .expect("read decremented account")
            .expect("account remains")
            .get_field_u32(get_field_by_symbol("sfOwnerCount")),
        1
    );

    let rules = built.rules().clone();
    cancel_tx
        .apply_with_tx_thread(
            &mut accumulated,
            Uint256::from_array([0x77; 32]),
            ledger_seq,
            &rules,
        )
        .expect("commit cancellation transaction");
    accumulated
        .apply_state_only(&mut built)
        .expect("publish accumulated state");
    assert!(
        built
            .read(offer_a_keylet)
            .expect("read removed offer")
            .is_none(),
        "OfferCreate A must be removed after cancellation"
    );
    let final_owner_page = built
        .read(owner_page_keylet)
        .expect("read surviving owner page")
        .expect("owner page 1 must remain for the successor offer");
    let final_indexes = final_owner_page.get_field_v256(get_field_by_symbol("sfIndexes"));
    assert!(!final_indexes.value().contains(&offer_a_keylet.key));
    assert!(final_indexes.value().contains(&successor_offer_keylet.key));
    assert_eq!(
        built
            .read(account_keylet)
            .expect("read final account")
            .expect("account remains")
            .get_field_u32(get_field_by_symbol("sfOwnerCount")),
        1
    );
}

#[test]
fn ledger_new_matches_narrow_cpp_map_roles() {
    let ledger = Ledger::new(
        LedgerHeader {
            seq: 500,
            ..LedgerHeader::default()
        },
        true,
    );

    assert_eq!(ledger.state_map().map_type(), SHAMapType::State);
    assert_eq!(ledger.tx_map().map_type(), SHAMapType::Transaction);
}

#[test]
fn ledger_set_immutable_with_rehash_pulls_map_hashes_into_header_and_hashes_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x71), vec![0x11; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x72), vec![0x22; 20]),
        0,
    );
    let tx_hash = tx_root.get_hash();
    let account_hash = state_root.get_hash();
    let mut expected_header = LedgerHeader {
        seq: 802,
        drops: 50,
        tx_hash,
        account_hash,
        parent_hash: sample_hash(0x73),
        parent_close_time: 60,
        close_time: 61,
        close_time_resolution: 62,
        close_flags: 63,
        ..LedgerHeader::default()
    };
    let expected_hash = calculate_ledger_hash(&expected_header);

    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 802,
            drops: 50,
            parent_hash: sample_hash(0x73),
            parent_close_time: 60,
            close_time: 61,
            close_time_resolution: 62,
            close_flags: 63,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            802,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            802,
            SyncState::Modifying,
        ),
    );

    ledger.set_immutable(true);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    expected_header.hash = expected_hash;
    assert_eq!(ledger.header(), expected_header);
}

#[test]
fn ledger_set_immutable_without_rehash_keeps_existing_header_hashes() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x81), vec![0x33; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x82), vec![0x44; 20]),
        0,
    );
    let original = LedgerHeader {
        seq: 803,
        hash: sample_hash(0x84),
        tx_hash: sample_hash(0x85),
        account_hash: sample_hash(0x86),
        ..LedgerHeader::default()
    };
    let mut ledger = Ledger::from_maps(
        original,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            803,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            803,
            SyncState::Modifying,
        ),
    );

    ledger.set_immutable(false);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    assert_eq!(ledger.header(), original);
}

#[test]
fn ledger_set_immutable_refreshes_rules_and_fees() {
    let preset_amendment = sample_uint256(0x87);
    let ledger_seq = 804;
    let original = LedgerHeader {
        seq: ledger_seq,
        hash: sample_hash(0x88),
        tx_hash: sample_hash(0x89),
        account_hash: sample_hash(0x8A),
        ..LedgerHeader::default()
    };
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), preset_amendment]),
            ),
            (
                fees_key(),
                encode_fee_settings_entry(
                    Fees {
                        base: 44,
                        reserve: 55,
                        increment: 66,
                    },
                    true,
                ),
            ),
        ],
        ledger_seq,
    );

    let mut ledger = Ledger::from_maps(
        original,
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, true, ledger_seq),
    );

    ledger.set_immutable(false);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().hash, original.hash);
    assert_eq!(ledger.header().tx_hash, original.tx_hash);
    assert_eq!(ledger.header().account_hash, original.account_hash);
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 44,
            reserve: 55,
            increment: 66,
        }
    );
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&preset_amendment));
}

#[test]
fn ledger_set_validated_flips_only_the_validated_flag() {
    let original = LedgerHeader {
        seq: 806,
        hash: sample_hash(0xB1),
        parent_hash: sample_hash(0xB2),
        tx_hash: sample_hash(0xB3),
        account_hash: sample_hash(0xB4),
        drops: 90,
        parent_close_time: 10,
        close_time: 20,
        close_time_resolution: 30,
        close_flags: SLCF_NO_CONSENSUS_TIME,
        ..LedgerHeader::default()
    };
    let mut ledger = Ledger::new(original, true);

    ledger.set_validated();

    assert!(ledger.header().validated);
    assert!(!ledger.header().accepted);
    assert_eq!(ledger.header().seq, original.seq);
    assert_eq!(ledger.header().hash, original.hash);
    assert_eq!(ledger.header().parent_hash, original.parent_hash);
    assert_eq!(ledger.header().tx_hash, original.tx_hash);
    assert_eq!(ledger.header().account_hash, original.account_hash);
    assert_eq!(ledger.header().drops, original.drops);
    assert_eq!(
        ledger.header().parent_close_time,
        original.parent_close_time
    );
    assert_eq!(ledger.header().close_time, original.close_time);
    assert_eq!(
        ledger.header().close_time_resolution,
        original.close_time_resolution
    );
    assert_eq!(ledger.header().close_flags, original.close_flags);
}
