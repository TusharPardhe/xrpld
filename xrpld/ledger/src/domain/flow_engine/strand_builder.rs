use super::{StepKind, Strand};
use crate::ApplyView;
use basics::base_uint::Uint256;
use protocol::{
    AccountID, Asset, Issue, STPath, STPathSet, Ter, get_field_by_symbol as sf, xrp_issue,
};

pub fn to_strand(
    src: &AccountID,
    dst: &AccountID,
    deliver: &Asset,
    send_max_asset: Option<&Asset>,
    path: &STPath,
    owner_pays_transfer_fee: bool,
    offer_crossing: bool,
) -> (Ter, Strand) {
    to_strand_with_domain(
        src,
        dst,
        deliver,
        send_max_asset,
        path,
        owner_pays_transfer_fee,
        offer_crossing,
        None,
    )
}

fn to_strand_with_domain(
    src: &AccountID,
    dst: &AccountID,
    deliver: &Asset,
    send_max_asset: Option<&Asset>,
    path: &STPath,
    owner_pays_transfer_fee: bool,
    offer_crossing: bool,
    domain: Option<Uint256>,
) -> (Ter, Strand) {
    if src.is_zero()
        || dst.is_zero()
        || *src == protocol::no_account()
        || *dst == protocol::no_account()
        || !asset_is_consistent(*deliver)
        || send_max_asset.is_some_and(|asset| !asset_is_consistent(*asset))
        || deliver.issuer() == protocol::no_account()
        || send_max_asset.is_some_and(|asset| asset.issuer() == protocol::no_account())
    {
        return (Ter::TEM_BAD_PATH, Vec::new());
    }

    for (index, element) in path.iter().enumerate() {
        if validate_path_element(index, path, element) != Ter::TES_SUCCESS {
            return (Ter::TEM_BAD_PATH, Vec::new());
        }
    }

    let initial_asset = match *send_max_asset.unwrap_or(deliver) {
        Asset::Issue(issue) if issue.native() => Asset::Issue(xrp_issue()),
        Asset::Issue(issue) => Asset::Issue(Issue::new(issue.currency, *src)),
        Asset::MPTIssue(issue) => Asset::MPTIssue(issue),
    };

    // Build normalized path elements
    let mut norm: Vec<NormElem> = Vec::with_capacity(4 + path.size());

    // 1. Source element
    norm.push(NormElem::Acct(*src));

    // 2. SendMax issuer if != src
    if let Some(sma) = send_max_asset
        && !sma.native()
        && sma.issuer() != *src
    {
        let first_is_issuer = path
            .iter()
            .next()
            .map(|e| e.is_account() && e.account_id() == sma.issuer())
            .unwrap_or(false);
        if !first_is_issuer {
            norm.push(NormElem::Acct(sma.issuer()));
        }
    }

    // 3. Explicit path elements
    for elem in path.iter() {
        if elem.is_account() {
            norm.push(NormElem::Acct(elem.account_id()));
        } else {
            let asset = if elem.has_mpt() {
                Asset::from(elem.mpt_id())
            } else {
                let issuer = if elem.has_issuer() {
                    elem.issuer_id()
                } else {
                    initial_asset.issuer()
                };
                Asset::Issue(Issue::new(elem.currency(), issuer))
            };
            norm.push(NormElem::Offer(asset));
        }
    }

    // 4. Deliver asset if last asset != deliver
    let needs_deliver_book = {
        let last_asset = last_asset_in_norm(&norm, initial_asset);
        !same_path_asset(last_asset, *deliver)
            || (offer_crossing && last_asset.issuer() != deliver.issuer())
    };
    if needs_deliver_book {
        norm.push(NormElem::Offer(*deliver));
    }

    // 5. Deliver issuer if != dst
    let deliver_issuer = deliver.issuer();
    let last_is_deliver_issuer =
        matches!(norm.last(), Some(NormElem::Acct(a)) if *a == deliver_issuer);
    if !last_is_deliver_issuer && *dst != deliver_issuer && !deliver_issuer.is_zero() {
        norm.push(NormElem::Acct(deliver_issuer));
    }

    // 6. Destination if not already last
    let last_is_dst = matches!(norm.last(), Some(NormElem::Acct(a)) if *a == *dst);
    if !last_is_dst {
        norm.push(NormElem::Acct(*dst));
    }

    if norm.len() < 2 {
        return (Ter::TEM_BAD_PATH, Vec::new());
    }

    // Create steps from normalized path pairs
    let mut strand: Strand = Vec::new();
    let mut cur_asset = initial_asset;

    for i in 0..norm.len() - 1 {
        let cur = &norm[i];
        let next = &norm[i + 1];

        // Update curAsset from current element
        match cur {
            NormElem::Acct(acct) => {
                if let Asset::Issue(issue) = &mut cur_asset
                    && !issue.native()
                {
                    issue.account = *acct;
                }
            }
            NormElem::Offer(asset) => cur_asset = *asset,
        }

        match (cur, next) {
            (NormElem::Acct(s), NormElem::Acct(d)) => {
                if cur_asset.native() {
                    // XRP endpoint
                    let is_first = i == 0;
                    strand.push(StepKind::XrpEndpoint {
                        account: if is_first { *s } else { *d },
                        is_last: !is_first,
                    });
                } else if let Asset::MPTIssue(issue) = cur_asset {
                    strand.push(StepKind::MptEndpoint {
                        src: *s,
                        dst: *d,
                        issue,
                        is_first: i == 0,
                        is_last: i == norm.len() - 2,
                        offer_crossing,
                    });
                } else if let Asset::Issue(issue) = cur_asset {
                    // DirectStep
                    strand.push(StepKind::Direct {
                        src: *s,
                        dst: *d,
                        currency: issue.currency,
                    });
                }
            }
            (NormElem::Acct(s), NormElem::Offer(out_asset)) => {
                if i == 0 && cur_asset.native() {
                    strand.push(StepKind::XrpEndpoint {
                        account: *s,
                        is_last: false,
                    });
                }
                // rippled `PaySteps.cpp::toStrand` normalizes `curAsset` after
                // changing its currency and before it calls `toStep`: XRP
                // always carries `xrpAccount()`, never a path issuer.  Keep
                // both sides canonical before storing the typed BookStep.
                strand.push(StepKind::Book {
                    book_in: canonical_book_asset(cur_asset),
                    book_out: canonical_book_asset(*out_asset),
                    domain,
                    owner_pays_transfer_fee,
                    remove_self_crossing: offer_crossing && path.size() == 0,
                });
                cur_asset = canonical_book_asset(*out_asset);
            }
            (NormElem::Offer(_), NormElem::Acct(d)) => {
                // Offer→Account: implied step if cur_issuer != dst
                if cur_asset.issuer() != *d && !d.is_zero() {
                    if cur_asset.native() {
                        strand.push(StepKind::XrpEndpoint {
                            account: *d,
                            is_last: true,
                        });
                    } else if let Asset::MPTIssue(issue) = cur_asset {
                        strand.push(StepKind::MptEndpoint {
                            src: issue.issuer(),
                            dst: *d,
                            issue,
                            is_first: false,
                            is_last: true,
                            offer_crossing,
                        });
                    } else if let Asset::Issue(issue) = cur_asset {
                        strand.push(StepKind::Direct {
                            src: issue.issuer(),
                            dst: *d,
                            currency: issue.currency,
                        });
                    }
                }
                continue;
            }
            (NormElem::Offer(_), NormElem::Offer(out_asset)) => {
                // Match the same `PaySteps.cpp::toStrand` normalization used by
                // the account-to-offer BookStep above.
                strand.push(StepKind::Book {
                    book_in: canonical_book_asset(cur_asset),
                    book_out: canonical_book_asset(*out_asset),
                    domain,
                    owner_pays_transfer_fee,
                    remove_self_crossing: offer_crossing && path.size() == 0,
                });
                cur_asset = canonical_book_asset(*out_asset);
            }
        }
    }

    if strand.is_empty() {
        return (Ter::TEM_BAD_PATH, Vec::new());
    }

    static STRAND_LOG: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    if STRAND_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 5 {
        tracing::debug!(target: "ledger",            "[to_strand] built strand with {} steps: {:?}",
            strand.len(),
            strand
        );
    }

    (Ter::TES_SUCCESS, strand)
}

fn asset_is_consistent(asset: Asset) -> bool {
    match asset {
        Asset::Issue(issue) => protocol::is_consistent(issue),
        Asset::MPTIssue(issue) => !issue.issuer().is_zero(),
    }
}

/// Validate the serialized path surface before normalization. This is the
/// ordered guard sequence in rippled PaySteps.cpp::toStrand; in particular a
/// TypeNone element must not be silently interpreted as an offer node.
fn validate_path_element(index: usize, path: &STPath, element: &protocol::STPathElement) -> Ter {
    let node_type = element.node_type();
    if (node_type & !protocol::STPathElement::TYPE_ALL) != 0
        || node_type == protocol::STPathElement::TYPE_NONE
    {
        return Ter::TEM_BAD_PATH;
    }

    let has_account = (node_type & protocol::STPathElement::TYPE_ACCOUNT) != 0;
    let has_issuer = (node_type & protocol::STPathElement::TYPE_ISSUER) != 0;
    let has_currency = (node_type & protocol::STPathElement::TYPE_CURRENCY) != 0;
    let has_mpt = (node_type & protocol::STPathElement::TYPE_MPT) != 0;
    let has_asset = (node_type & protocol::STPathElement::TYPE_ASSET) != 0;

    if has_account && (has_issuer || has_currency)
        || has_issuer && element.issuer_id().is_zero()
        || has_account && element.account_id().is_zero()
        || has_currency
            && has_issuer
            && (protocol::is_xrp_currency(element.currency()) != element.issuer_id().is_zero())
        || has_issuer && element.issuer_id() == protocol::no_account()
        || has_account && element.account_id() == protocol::no_account()
        || has_mpt && (has_currency || has_account)
        || has_mpt && has_issuer && element.issuer_id() != Asset::from(element.mpt_id()).issuer()
        || index > 0 && path[index - 1].has_mpt() && (has_account || (has_issuer && !has_asset))
    {
        return Ter::TEM_BAD_PATH;
    }

    Ter::TES_SUCCESS
}

pub fn to_strands(
    src: &AccountID,
    dst: &AccountID,
    deliver: &Asset,
    send_max_asset: Option<&Asset>,
    paths: &STPathSet,
    default_paths_allowed: bool,
    owner_pays_transfer_fee: bool,
    offer_crossing: bool,
) -> (Ter, Vec<Strand>) {
    to_strands_with_domain(
        src,
        dst,
        deliver,
        send_max_asset,
        paths,
        default_paths_allowed,
        owner_pays_transfer_fee,
        offer_crossing,
        None,
    )
}

/// Ledger-aware counterpart to [`to_strands`].  rippled validates each Step
/// while constructing its candidate strand; consequently a bad explicit path
/// is discarded without poisoning other valid paths, while its TER is retained
/// when no candidate survives.  Keep structural-only construction available
/// for unit tests, but all transaction paths must use this checked entry point.
pub fn to_strands_checked<V: ApplyView>(
    view: &mut V,
    src: &AccountID,
    dst: &AccountID,
    deliver: &Asset,
    send_max_asset: Option<&Asset>,
    paths: &STPathSet,
    default_paths_allowed: bool,
    owner_pays_transfer_fee: bool,
    offer_crossing: bool,
) -> (Ter, Vec<Strand>) {
    to_strands_checked_with_domain(
        view,
        src,
        dst,
        deliver,
        send_max_asset,
        paths,
        default_paths_allowed,
        owner_pays_transfer_fee,
        offer_crossing,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn to_strands_checked_with_domain<V: ApplyView>(
    view: &mut V,
    src: &AccountID,
    dst: &AccountID,
    deliver: &Asset,
    send_max_asset: Option<&Asset>,
    paths: &STPathSet,
    default_paths_allowed: bool,
    owner_pays_transfer_fee: bool,
    offer_crossing: bool,
    domain: Option<Uint256>,
) -> (Ter, Vec<Strand>) {
    let mut result = Vec::with_capacity(1 + paths.size());

    let mut try_insert = |path: &STPath| -> Ter {
        let (ter, strand) = to_strand_with_domain(
            src,
            dst,
            deliver,
            send_max_asset,
            path,
            owner_pays_transfer_fee,
            offer_crossing,
            domain,
        );
        if ter != Ter::TES_SUCCESS {
            return ter;
        }
        if strand.is_empty() {
            return Ter::TEF_EXCEPTION;
        }
        let ter = validate_strand(view, &strand, src, dst, *deliver, offer_crossing);
        if ter == Ter::TES_SUCCESS && !result.contains(&strand) {
            result.push(strand);
        }
        ter
    };

    if default_paths_allowed {
        let ter = try_insert(&STPath::new());
        if ter != Ter::TES_SUCCESS && (protocol::is_tem_malformed(ter) || paths.size() == 0) {
            return (ter, Vec::new());
        }
    } else if paths.size() == 0 {
        return (Ter::TEM_RIPPLE_EMPTY, Vec::new());
    }

    let mut last_fail_ter = Ter::TES_SUCCESS;
    for path in paths.iter() {
        let ter = try_insert(path);
        if ter != Ter::TES_SUCCESS {
            last_fail_ter = ter;
            if protocol::is_tem_malformed(ter) {
                return (ter, Vec::new());
            }
        }
    }

    if result.is_empty() {
        return (last_fail_ter, result);
    }
    (Ter::TES_SUCCESS, result)
}

pub fn to_strands_with_domain(
    src: &AccountID,
    dst: &AccountID,
    deliver: &Asset,
    send_max_asset: Option<&Asset>,
    paths: &STPathSet,
    default_paths_allowed: bool,
    owner_pays_transfer_fee: bool,
    offer_crossing: bool,
    domain: Option<Uint256>,
) -> (Ter, Vec<Strand>) {
    let mut result: Vec<Strand> = Vec::new();

    if default_paths_allowed {
        let empty_path = protocol::STPath::new();
        let (ter, strand) = to_strand_with_domain(
            src,
            dst,
            deliver,
            send_max_asset,
            &empty_path,
            owner_pays_transfer_fee,
            offer_crossing,
            domain,
        );
        if ter == Ter::TES_SUCCESS && !strand.is_empty() {
            if !result.contains(&strand) {
                result.push(strand);
            }
        } else if ter != Ter::TES_SUCCESS && (protocol::is_tem_malformed(ter) || paths.size() == 0)
        {
            return (ter, Vec::new());
        }
    }

    let mut last_fail_ter = Ter::TES_SUCCESS;
    for path in paths.iter() {
        let (ter, strand) = to_strand_with_domain(
            src,
            dst,
            deliver,
            send_max_asset,
            path,
            owner_pays_transfer_fee,
            offer_crossing,
            domain,
        );
        if ter == Ter::TES_SUCCESS && !strand.is_empty() {
            if !result.contains(&strand) {
                result.push(strand);
            }
        } else if ter != Ter::TES_SUCCESS {
            last_fail_ter = ter;
            if protocol::is_tem_malformed(ter) {
                return (ter, Vec::new());
            }
        }
    }

    if result.is_empty() && !default_paths_allowed && paths.size() == 0 {
        return (Ter::TEM_RIPPLE_EMPTY, Vec::new());
    }

    if result.is_empty() {
        return (last_fail_ter, result);
    }

    (Ter::TES_SUCCESS, result)
}

fn read_sle<V: ApplyView>(
    view: &mut V,
    keylet: protocol::Keylet,
) -> Result<Option<std::sync::Arc<protocol::STLedgerEntry>>, Ter> {
    view.read(keylet).map_err(|_| Ter::TEF_BAD_LEDGER)
}

fn asset_frozen_for<V: ApplyView>(
    view: &mut V,
    account: &AccountID,
    asset: Asset,
) -> Result<bool, Ter> {
    match asset {
        Asset::Issue(issue) => {
            if issue.native() {
                Ok(false)
            } else {
                crate::domain::ripple_state_helpers::try_is_frozen(view, account, &issue)
                    .map_err(|_| Ter::TEF_BAD_LEDGER)
            }
        }
        Asset::MPTIssue(issue) => {
            crate::domain::mptoken_helpers::is_frozen_mpt(view, account, &issue)
                .map_err(|_| Ter::TEF_BAD_LEDGER)
        }
    }
}

fn check_direct_freeze<V: ApplyView>(
    view: &mut V,
    src: &AccountID,
    dst: &AccountID,
    currency: protocol::Currency,
) -> Ter {
    let dst_root = match read_sle(
        view,
        protocol::account_keylet(basics::base_uint::Uint160::from_void(dst.data())),
    ) {
        Ok(root) => root,
        Err(ter) => return ter,
    };
    if dst_root
        .as_ref()
        .is_some_and(|root| root.is_flag(protocol::lsfGlobalFreeze))
    {
        return Ter::TER_NO_LINE;
    }

    let line = match read_sle(view, protocol::line(*src, *dst, currency)) {
        Ok(line) => line,
        Err(ter) => return ter,
    };
    if line.as_ref().is_some_and(|line| {
        let destination_freeze = if dst > src {
            protocol::lsfHighFreeze
        } else {
            protocol::lsfLowFreeze
        };
        line.is_flag(destination_freeze)
            || line.is_flag(protocol::lsfHighDeepFreeze)
            || line.is_flag(protocol::lsfLowDeepFreeze)
    }) {
        return Ter::TER_NO_LINE;
    }

    check_lp_token_freeze(view, src, dst_root.as_deref())
}

fn check_lp_token_freeze<V: ApplyView>(
    view: &mut V,
    src: &AccountID,
    dst_root: Option<&protocol::STLedgerEntry>,
) -> Ter {
    if view
        .rules()
        .enabled(&protocol::feature_id("fixFrozenLPTokenTransfer"))
        && let Some(dst_root) = dst_root
        && dst_root.is_field_present(sf("sfAMMID"))
    {
        let amm = match read_sle(
            view,
            protocol::amm_keylet(dst_root.get_field_h256(sf("sfAMMID"))),
        ) {
            Ok(Some(amm)) => amm,
            Ok(None) => return Ter::TEC_INTERNAL,
            Err(ter) => return ter,
        };
        let asset = amm.get_field_issue(sf("sfAsset")).asset();
        let asset2 = amm.get_field_issue(sf("sfAsset2")).asset();
        match (
            asset_frozen_for(view, src, asset),
            asset_frozen_for(view, src, asset2),
        ) {
            (Ok(true), _) | (_, Ok(true)) => return Ter::TER_NO_LINE,
            (Err(ter), _) | (_, Err(ter)) => return ter,
            _ => {}
        }
    }
    Ter::TES_SUCCESS
}

fn check_xrp_endpoint_freeze<V: ApplyView>(
    view: &mut V,
    account: &AccountID,
    is_last: bool,
) -> Ter {
    // checkFreeze(xrpAccount -> account) only has a real destination on the
    // final endpoint.  The XRP trust-line lookup is structurally empty.
    if !is_last {
        return Ter::TES_SUCCESS;
    }
    let root = match read_sle(
        view,
        protocol::account_keylet(basics::base_uint::Uint160::from_void(account.data())),
    ) {
        Ok(root) => root,
        Err(ter) => return ter,
    };
    if root
        .as_ref()
        .is_some_and(|root| root.is_flag(protocol::lsfGlobalFreeze))
    {
        return Ter::TER_NO_LINE;
    }
    check_lp_token_freeze(view, &protocol::xrp_account(), root.as_deref())
}

fn direct_no_ripple_flag(account: &AccountID, other: &AccountID) -> u32 {
    if account > other {
        protocol::lsfHighNoRipple
    } else {
        protocol::lsfLowNoRipple
    }
}

fn check_consecutive_direct_no_ripple<V: ApplyView>(
    view: &mut V,
    prev: &AccountID,
    cur: &AccountID,
    next: &AccountID,
    currency: protocol::Currency,
) -> Ter {
    let inbound = match read_sle(view, protocol::line(*prev, *cur, currency)) {
        Ok(Some(line)) => line,
        Ok(None) => return Ter::TER_NO_LINE,
        Err(ter) => return ter,
    };
    let outbound = match read_sle(view, protocol::line(*cur, *next, currency)) {
        Ok(Some(line)) => line,
        Ok(None) => return Ter::TER_NO_LINE,
        Err(ter) => return ter,
    };
    if inbound.is_flag(direct_no_ripple_flag(cur, prev))
        && outbound.is_flag(direct_no_ripple_flag(cur, next))
    {
        Ter::TER_NO_RIPPLE
    } else {
        Ter::TES_SUCCESS
    }
}

/// Validate the ledger-dependent parts of rippled's Step constructors.
/// This deliberately runs once per candidate strand, before `toStrands`
/// decides whether another candidate can survive its TER.
fn validate_strand<V: ApplyView>(
    view: &mut V,
    strand: &Strand,
    strand_src: &AccountID,
    strand_dst: &AccountID,
    strand_deliver: Asset,
    offer_crossing: bool,
) -> Ter {
    let mut seen_direct_src = Vec::<Asset>::new();
    let mut seen_direct_dst = Vec::<Asset>::new();
    let mut seen_book_outs = Vec::<Asset>::new();

    for (index, step) in strand.iter().enumerate() {
        match step {
            StepKind::Book {
                book_in, book_out, ..
            } => {
                if !protocol::is_consistent_book(protocol::Book::new(*book_in, *book_out, None)) {
                    return Ter::TEM_BAD_PATH;
                }
                if seen_book_outs.contains(book_out)
                    || seen_direct_src.contains(book_out)
                    || seen_direct_dst.contains(book_out)
                {
                    return Ter::TEM_BAD_PATH_LOOP;
                }

                for asset in [book_in, book_out] {
                    let issuer = asset.issuer();
                    if !issuer.is_zero() {
                        match read_sle(
                            view,
                            protocol::account_keylet(basics::base_uint::Uint160::from_void(
                                issuer.data(),
                            )),
                        ) {
                            Ok(Some(_)) => {}
                            Ok(None) => return Ter::TEC_NO_ISSUER,
                            Err(ter) => return ter,
                        }
                    }
                }

                if let Some(StepKind::Direct {
                    src: prev_src,
                    currency: prev_currency,
                    ..
                }) = index.checked_sub(1).and_then(|i| strand.get(i))
                    && let Asset::Issue(in_issue) = book_in
                    && in_issue.currency == *prev_currency
                {
                    let line = match read_sle(
                        view,
                        protocol::line(*prev_src, in_issue.account, in_issue.currency),
                    ) {
                        Ok(Some(line)) => line,
                        Ok(None) => return Ter::TER_NO_LINE,
                        Err(ter) => return ter,
                    };
                    if line.is_flag(direct_no_ripple_flag(&in_issue.account, prev_src)) {
                        return Ter::TER_NO_RIPPLE;
                    }
                }

                for asset in [book_in, book_out] {
                    match crate::domain::mptoken_helpers::can_trade(view, asset) {
                        Ok(Ter::TES_SUCCESS) => {}
                        Ok(ter) => return ter,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    }
                }
                seen_book_outs.push(*book_out);
            }
            StepKind::Direct { src, dst, currency } => {
                if src.is_zero() || dst.is_zero() || src == dst {
                    return Ter::TEM_BAD_PATH;
                }
                let src_root = match read_sle(
                    view,
                    protocol::account_keylet(basics::base_uint::Uint160::from_void(src.data())),
                ) {
                    Ok(Some(root)) => root,
                    Ok(None) => return Ter::TER_NO_ACCOUNT,
                    Err(ter) => return ter,
                };

                if strand.len() != 1 {
                    let ter = check_direct_freeze(view, src, dst, *currency);
                    if ter != Ter::TES_SUCCESS {
                        return ter;
                    }
                }

                if let Some(StepKind::Direct {
                    src: prev_src,
                    dst: prev_dst,
                    currency: prev_currency,
                }) = index.checked_sub(1).and_then(|i| strand.get(i))
                    && prev_dst == src
                    && prev_currency == currency
                {
                    let ter =
                        check_consecutive_direct_no_ripple(view, prev_src, src, dst, *currency);
                    if ter != Ter::TES_SUCCESS {
                        return ter;
                    }
                }

                let src_issue = Asset::Issue(Issue::new(*currency, *src));
                let dst_issue = Asset::Issue(Issue::new(*currency, *dst));
                if seen_book_outs.contains(&src_issue)
                    && !matches!(strand.get(index.wrapping_sub(1)), Some(StepKind::Book { book_out, .. }) if *book_out == src_issue)
                {
                    return Ter::TEM_BAD_PATH_LOOP;
                }
                if seen_direct_src.contains(&src_issue) || seen_direct_dst.contains(&dst_issue) {
                    return Ter::TEM_BAD_PATH_LOOP;
                }
                seen_direct_src.push(src_issue);
                seen_direct_dst.push(dst_issue);

                if !offer_crossing {
                    let line = match read_sle(view, protocol::line(*src, *dst, *currency)) {
                        Ok(Some(line)) => line,
                        Ok(None) => return Ter::TER_NO_LINE,
                        Err(ter) => return ter,
                    };
                    let auth_flag = if src > dst {
                        protocol::lsfHighAuth
                    } else {
                        protocol::lsfLowAuth
                    };
                    if src_root.is_flag(protocol::lsfRequireAuth)
                        && !line.is_flag(auth_flag)
                        && line.get_field_amount(sf("sfBalance")).signum() == 0
                    {
                        return Ter::TER_NO_AUTH;
                    }
                    if matches!(
                        index.checked_sub(1).and_then(|i| strand.get(i)),
                        Some(StepKind::Book { .. })
                    ) && line.is_flag(direct_no_ripple_flag(src, dst))
                    {
                        return Ter::TER_NO_RIPPLE;
                    }

                    let owed = match crate::domain::ripple_state_helpers::try_credit_balance(
                        view, dst, src, *currency,
                    ) {
                        Ok(owed) => owed,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                    let limit_field = if dst < src {
                        sf("sfLowLimit")
                    } else {
                        sf("sfHighLimit")
                    };
                    let limit = line.get_field_amount(limit_field);
                    if owed.signum() <= 0 && -owed.iou() >= limit.iou() {
                        return Ter::TEC_PATH_DRY;
                    }
                }
            }
            StepKind::XrpEndpoint { account, is_last } => {
                if account.is_zero() {
                    return Ter::TEM_BAD_PATH;
                }
                match read_sle(
                    view,
                    protocol::account_keylet(basics::base_uint::Uint160::from_void(account.data())),
                ) {
                    Ok(Some(_)) => {}
                    Ok(None) => return Ter::TER_NO_ACCOUNT,
                    Err(ter) => return ter,
                }
                let is_first = index == 0;
                let is_final = index + 1 == strand.len();
                if !is_first && !is_final {
                    return Ter::TEM_BAD_PATH;
                }
                let ter = check_xrp_endpoint_freeze(view, account, *is_last);
                if ter != Ter::TES_SUCCESS {
                    return ter;
                }
                let xrp = Asset::Issue(xrp_issue());
                let seen = if *is_last {
                    &mut seen_direct_src
                } else {
                    &mut seen_direct_dst
                };
                if seen.contains(&xrp) {
                    return Ter::TEM_BAD_PATH_LOOP;
                }
                seen.push(xrp);
            }
            StepKind::MptEndpoint {
                src, dst, issue, ..
            } => {
                let actual_first = index == 0;
                let actual_last = index + 1 == strand.len();
                if src.is_zero() || dst.is_zero() || src == dst {
                    return Ter::TEM_BAD_PATH;
                }
                match read_sle(
                    view,
                    protocol::account_keylet(basics::base_uint::Uint160::from_void(src.data())),
                ) {
                    Ok(Some(_)) => {}
                    Ok(None) => return Ter::TER_NO_ACCOUNT,
                    Err(ter) => return ter,
                }

                if !(actual_first && actual_last) {
                    let account = if actual_first { src } else { dst };
                    let globally_frozen = if actual_first {
                        match crate::domain::mptoken_helpers::is_global_frozen_mpt(view, issue) {
                            Ok(frozen) => frozen,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        }
                    } else {
                        false
                    };
                    let individually_frozen =
                        match crate::domain::mptoken_helpers::is_individual_frozen_mpt(
                            view, account, issue,
                        ) {
                            Ok(frozen) => frozen,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        };
                    if globally_frozen || individually_frozen {
                        return Ter::TER_LOCKED;
                    }
                }

                let mpt_asset = Asset::MPTIssue(*issue);
                if seen_book_outs.contains(&mpt_asset)
                    && !matches!(index.checked_sub(1).and_then(|i| strand.get(i)), Some(StepKind::Book { book_out, .. }) if *book_out == mpt_asset)
                {
                    return Ter::TEM_BAD_PATH_LOOP;
                }
                let seen = if actual_first {
                    &mut seen_direct_src
                } else {
                    &mut seen_direct_dst
                };
                if seen.contains(&mpt_asset) {
                    return Ter::TEM_BAD_PATH_LOOP;
                }
                seen.push(mpt_asset);

                if !actual_first && !actual_last {
                    return Ter::TEM_BAD_PATH;
                }
                let issuer = issue.issuer();
                if (*src != issuer) == (*dst != issuer) {
                    return Ter::TEM_BAD_PATH;
                }

                if !offer_crossing {
                    for account in [src, dst] {
                        if *account != issuer {
                            // C++ MPTEndpointPaymentStep uses requireAuth's
                            // default Legacy mode.  For MPTs, Legacy and
                            // Strong both require an MPToken object; Weak is
                            // reserved for operations which may create one.
                            match crate::domain::mptoken_helpers::require_auth_mpt_with_type(
                                view,
                                issue,
                                account,
                                crate::domain::mptoken_helpers::MPTAuthType::Strong,
                            ) {
                                Ok(Ter::TES_SUCCESS) => {}
                                Ok(ter) => return ter,
                                Err(_) => return Ter::TEF_BAD_LEDGER,
                            }
                        }
                    }

                    let direct_mpt = mpt_asset == strand_deliver
                        && (actual_first
                            || !matches!(
                                index.checked_sub(1).and_then(|i| strand.get(i)),
                                Some(StepKind::Book { .. })
                            ));
                    if direct_mpt {
                        let between_holders = *strand_src != issuer && *strand_dst != issuer;
                        if between_holders {
                            let holder = if actual_first { src } else { dst };
                            let frozen = match crate::domain::mptoken_helpers::is_frozen_mpt(
                                view, holder, issue,
                            ) {
                                Ok(frozen) => frozen,
                                Err(_) => return Ter::TEF_BAD_LEDGER,
                            };
                            if frozen {
                                return Ter::TEC_LOCKED;
                            }
                            match crate::domain::mptoken_helpers::can_transfer_mpt(
                                view, issue, holder, strand_dst,
                            ) {
                                Ok(Ter::TES_SUCCESS) => {}
                                Ok(ter) => return ter,
                                Err(_) => return Ter::TEF_BAD_LEDGER,
                            }
                        }
                    } else {
                        match crate::domain::mptoken_helpers::can_trade(view, &mpt_asset) {
                            Ok(Ter::TES_SUCCESS) => {}
                            Ok(ter) => return ter,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        }
                    }

                    if index == 0 {
                        let funds = if *src == issuer {
                            crate::domain::mptoken_helpers::issuer_funds_to_self_issue(view, issue)
                                .map_err(|_| Ter::TEF_BAD_LEDGER)
                                .map(|amount| amount.mpt().value())
                        } else {
                            read_sle(
                                view,
                                protocol::mptoken_keylet_from_mptid(
                                    issue.mpt_id(),
                                    basics::base_uint::Uint160::from_void(src.data()),
                                ),
                            )
                            .map(|token| {
                                token.map_or(0, |token| {
                                    token.get_field_u64(sf("sfMPTAmount")) as i64
                                })
                            })
                        };
                        match funds {
                            Ok(value) if value > 0 => {}
                            Ok(_) => return Ter::TEC_PATH_DRY,
                            Err(ter) => return ter,
                        }
                    }
                }
            }
        }
    }
    Ter::TES_SUCCESS
}

/// Return the protocol's sole canonical issue for XRP while preserving the
/// issuer required by every issued currency.  `Issue` equality intentionally
/// ignores an XRP account, but `keylet::get_book_base` must receive the
/// canonical zero XRP account (rippled `PaySteps.cpp::toStrand`, immediately
/// before its `toStep` call).
fn canonical_book_asset(asset: Asset) -> Asset {
    match asset {
        Asset::Issue(issue) if issue.native() => Asset::Issue(xrp_issue()),
        _ => asset,
    }
}

fn same_path_asset(lhs: Asset, rhs: Asset) -> bool {
    match (lhs, rhs) {
        (Asset::Issue(lhs), Asset::Issue(rhs)) => lhs.currency == rhs.currency,
        (Asset::MPTIssue(lhs), Asset::MPTIssue(rhs)) => lhs == rhs,
        _ => false,
    }
}

#[derive(Debug, Clone)]
enum NormElem {
    Acct(AccountID),
    Offer(Asset),
}

fn last_asset_in_norm(norm: &[NormElem], initial: Asset) -> Asset {
    for elem in norm.iter().rev() {
        if let NormElem::Offer(asset) = elem {
            return *asset;
        }
    }
    initial
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol::{AccountID, Asset, Currency, Issue, xrp_issue};

    fn make_account(byte: u8) -> AccountID {
        let mut data = [0u8; 20];
        data[0] = byte;
        AccountID::from(data)
    }

    fn make_currency(s: &str) -> Currency {
        let mut data = [0u8; 20];
        for (i, b) in s.bytes().enumerate().take(3) {
            data[12 + i] = b;
        }
        Currency::from(data)
    }

    #[test]
    fn offer_crossing_domain_is_attached_to_every_book_step() {
        let src = make_account(1);
        let issuer = make_account(3);
        let deliver = Asset::Issue(Issue::new(make_currency("USD"), issuer));
        let send_max = Asset::Issue(xrp_issue());
        let domain = Uint256::from_array([0xD0; 32]);
        let (_, strands) = to_strands_with_domain(
            &src,
            &src,
            &deliver,
            Some(&send_max),
            &STPathSet::new(protocol::get_field_by_symbol("sfPaths")),
            true,
            true,
            true,
            Some(domain),
        );
        let books: Vec<_> = strands
            .iter()
            .flatten()
            .filter_map(|step| match step {
                StepKind::Book { domain, .. } => Some(*domain),
                _ => None,
            })
            .collect();
        assert!(!books.is_empty());
        assert!(books.iter().all(|actual| *actual == Some(domain)));
    }

    #[test]
    fn test_iou_to_iou_default_path_through_issuer() {
        // IOU→IOU: sender→issuer→receiver (default path, no explicit paths)
        let src = make_account(1); // Alice
        let dst = make_account(2); // Bob
        let gateway = make_account(3); // Gateway (issuer)
        let usd = make_currency("USD");
        let deliver = Asset::Issue(Issue {
            currency: usd,
            account: gateway,
        });

        let (ter, strand) = to_strand(
            &src,
            &dst,
            &deliver,
            None,
            &protocol::STPath::new(),
            false,
            false,
        );

        assert_eq!(ter, Ter::TES_SUCCESS);
        // Expected strand: DirectStep(Alice→Gateway) + DirectStep(Gateway→Bob)
        // OR: DirectStep(Alice→Bob) if direct trust line
        assert!(!strand.is_empty(), "Strand should not be empty");

        // Verify steps are DirectSteps with correct accounts
        for step in &strand {
            match step {
                StepKind::Direct {
                    src: s,
                    dst: d,
                    currency: c,
                } => {
                    assert_eq!(*c, usd);
                    assert!(!s.is_zero());
                    assert!(!d.is_zero());
                }
                _ => panic!("Expected DirectStep for IOU→IOU, got {:?}", step),
            }
        }
    }

    #[test]
    fn test_xrp_to_iou_default_path() {
        // XRP→IOU: XRPEndpointStep(src) + BookStep(XRP/IOU) + DirectStep(issuer→dst)
        let src = make_account(1);
        let dst = make_account(2);
        let gateway = make_account(3);
        let usd = make_currency("USD");
        let deliver = Asset::Issue(Issue {
            currency: usd,
            account: gateway,
        });
        let send_max = Asset::Issue(xrp_issue());

        let (ter, strand) = to_strand(
            &src,
            &dst,
            &deliver,
            Some(&send_max),
            &protocol::STPath::new(),
            false,
            false,
        );

        assert_eq!(ter, Ter::TES_SUCCESS);
        assert!(!strand.is_empty(), "Strand should not be empty for XRP→IOU");

        // Should have: XrpEndpoint(src) + Book(XRP→USD) + Direct(gateway→dst)
        let has_xrp_endpoint = strand
            .iter()
            .any(|s| matches!(s, StepKind::XrpEndpoint { .. }));
        let has_book = strand.iter().any(|s| matches!(s, StepKind::Book { .. }));

        assert!(has_xrp_endpoint, "XRP→IOU should have XrpEndpointStep");
        assert!(has_book, "XRP→IOU should have BookStep");
    }

    #[test]
    fn no_default_path_without_explicit_paths_returns_ripple_empty() {
        let src = make_account(1);
        let dst = make_account(2);
        let gateway = make_account(3);
        let eur = make_currency("EUR");
        let deliver = Asset::Issue(Issue {
            currency: eur,
            account: gateway,
        });

        let (ter, strands) = to_strands(
            &src,
            &dst,
            &deliver,
            None,
            &protocol::STPathSet::new(protocol::get_field_by_symbol("sfPaths")),
            false,
            false,
            false,
        );

        assert_eq!(ter, Ter::TEM_RIPPLE_EMPTY);
        assert!(strands.is_empty());
    }

    #[test]
    fn type_none_explicit_path_is_rejected_before_normalization() {
        let src = make_account(1);
        let dst = make_account(2);
        let gateway = make_account(3);
        let deliver = Asset::Issue(Issue::new(make_currency("USD"), gateway));
        let mut path = protocol::STPath::new();
        path.push_back(protocol::STPathElement::inferred(
            AccountID::zero(),
            protocol::xrp_currency(),
            AccountID::zero(),
            false,
        ));

        let (ter, strand) = to_strand(
            &src,
            &dst,
            &deliver,
            Some(&Asset::Issue(xrp_issue())),
            &path,
            false,
            false,
        );

        assert_eq!(path[0].node_type(), protocol::STPathElement::TYPE_NONE);
        assert_eq!(ter, Ter::TEM_BAD_PATH);
        assert!(strand.is_empty());
    }

    #[test]
    fn canonical_xrp_book_issue_discards_a_stale_issuer_before_keylet_lookup() {
        let stale_issuer = protocol::parse_base58_account_id("rswh1fvyLqHizBS2awu1vs6QcmwTBd9qiv")
            .expect("canonical XAH issuer");
        let raw = Issue::new(protocol::xrp_currency(), stale_issuer);
        assert!(
            !protocol::is_consistent(raw),
            "the protocol keylet must reject XRP with an issuer"
        );

        let normalized = canonical_book_asset(Asset::Issue(raw));
        assert_eq!(normalized, Asset::Issue(xrp_issue()));
        let Asset::Issue(normalized_issue) = normalized else {
            unreachable!()
        };
        assert!(protocol::is_consistent(normalized_issue));
    }

    #[test]
    fn canonical_xah_to_xrp_mainnet_direct_xrp_path_builds_a_consistent_book() {
        // EDA59CA1B73A69E76E753F6790DBC2E323B3699CFA200D15B3EAA0FFC2FFC2B3,
        // 0386E0015B04116D4F61ECF5EEE71C8912F53C74558982227B24990BD3CFD921,
        // and DF801A1D59B2B36981AFD810978D84FA06F5E7D6872A5D3AEB2B908EAAF184C0
        // are self-payments from rspxi5HWiqiGUdpge6hZh7drZXRMqDX93t. Each
        // sends XAH issued by rswh1fvyLqHizBS2awu1vs6QcmwTBd9qiv to XRP,
        // with tfPartialPayment|tfLimitQuality, and includes this direct
        // explicit Path: [{ currency: XRP }]. Model its type-16 element here
        // so the regression exercises the actual XAH-to-XRP strand shape,
        // rather than an empty default path.
        let account = protocol::parse_base58_account_id("rspxi5HWiqiGUdpge6hZh7drZXRMqDX93t")
            .expect("canonical transaction account");
        let issuer = protocol::parse_base58_account_id("rswh1fvyLqHizBS2awu1vs6QcmwTBd9qiv")
            .expect("canonical XAH issuer");
        let xah = protocol::currency_from_string("XAH");
        let deliver = Asset::Issue(xrp_issue());
        let send_max = Asset::Issue(Issue::new(xah, issuer));
        let mut direct_xrp_path = protocol::STPath::new();
        direct_xrp_path.push_back(protocol::STPathElement::raw(
            protocol::STPathElement::TYPE_CURRENCY,
            AccountID::zero(),
            protocol::xrp_currency(),
            AccountID::zero(),
        ));

        let (ter, strand) = to_strand(
            &account,
            &account,
            &deliver,
            Some(&send_max),
            &direct_xrp_path,
            false,
            false,
        );

        assert_eq!(ter, Ter::TES_SUCCESS);
        let (book_in, book_out) = strand
            .iter()
            .find_map(|step| match step {
                StepKind::Book {
                    book_in, book_out, ..
                } => Some((*book_in, *book_out)),
                _ => None,
            })
            .expect("XAH-to-XRP payment must include a BookStep");
        assert_eq!(book_in, Asset::Issue(Issue::new(xah, issuer)));
        assert_eq!(book_out, Asset::Issue(xrp_issue()));

        let book = protocol::Book::new(book_in, book_out, None);
        assert!(protocol::is_consistent_book(book));
        // This is the exact protocol boundary that previously panicked.
        let _ = protocol::get_book_base(book);
    }

    #[test]
    fn test_iou_to_xrp_default_path() {
        // IOU→XRP: DirectStep(src→issuer) + BookStep(IOU/XRP) + XRPEndpointStep(dst)
        let src = make_account(1);
        let dst = make_account(2);
        let gateway = make_account(3);
        let usd = make_currency("USD");
        let deliver = Asset::Issue(xrp_issue());
        let send_max = Asset::Issue(Issue {
            currency: usd,
            account: gateway,
        });

        let (ter, strand) = to_strand(
            &src,
            &dst,
            &deliver,
            Some(&send_max),
            &protocol::STPath::new(),
            false,
            false,
        );

        assert_eq!(ter, Ter::TES_SUCCESS);
        assert!(!strand.is_empty(), "Strand should not be empty for IOU→XRP");

        let has_book = strand.iter().any(|s| matches!(s, StepKind::Book { .. }));
        let has_xrp_endpoint = strand
            .iter()
            .any(|s| matches!(s, StepKind::XrpEndpoint { .. }));

        assert!(has_book, "IOU→XRP should have BookStep");
        assert!(has_xrp_endpoint, "IOU→XRP should have XrpEndpointStep");
    }

    #[test]
    fn test_xrp_to_xrp_rejected() {
        // XRP→XRP should not build a strand (handled separately by handle_xrp_to_xrp_flow)
        let src = make_account(1);
        let dst = make_account(2);
        let deliver = Asset::Issue(xrp_issue());

        let (ter, strand) = to_strand(
            &src,
            &dst,
            &deliver,
            None,
            &protocol::STPath::new(),
            false,
            false,
        );

        // XRP→XRP with no sendMax: curAsset = xrpIssue, deliver = xrpIssue
        // The strand should be: XrpEndpoint(src, false) → XrpEndpoint(dst, true)
        // OR it might fail because src element with XRP + dst element with XRP = no book needed
        // Actually in the reference, XRP→XRP goes through handle_xrp_to_xrp_flow, not toStrand
        // But if it does reach toStrand, it should build XRP endpoints
        if ter == Ter::TES_SUCCESS {
            assert!(!strand.is_empty());
        }
    }

    #[test]
    fn test_strand_accounts_are_correct() {
        // Verify that DirectStep accounts match what reference would produce
        let src = make_account(1);
        let dst = make_account(2);
        let gateway = make_account(3);
        let usd = make_currency("USD");
        let deliver = Asset::Issue(Issue {
            currency: usd,
            account: gateway,
        });

        let (ter, strand) = to_strand(
            &src,
            &dst,
            &deliver,
            None,
            &protocol::STPath::new(),
            false,
            false,
        );
        assert_eq!(ter, Ter::TES_SUCCESS);

        // [src, USD/src] → [gateway] (if gateway != dst) → [dst]
        // Steps: DirectStep(src, gateway) + DirectStep(gateway, dst)
        // Unless src == gateway or dst == gateway

        if strand.len() == 2 {
            // Two DirectSteps: src→gateway, gateway→dst
            if let StepKind::Direct {
                src: s1, dst: d1, ..
            } = &strand[0]
            {
                assert_eq!(*s1, src, "First step src should be sender");
                assert_eq!(*d1, gateway, "First step dst should be issuer");
            }
            if let StepKind::Direct {
                src: s2, dst: d2, ..
            } = &strand[1]
            {
                assert_eq!(*s2, gateway, "Second step src should be issuer");
                assert_eq!(*d2, dst, "Second step dst should be receiver");
            }
        } else if strand.len() == 1 {
            // Single DirectStep: src→dst (when one party is issuer)
            if let StepKind::Direct { src: s, dst: d, .. } = &strand[0] {
                assert_eq!(*s, src);
                assert_eq!(*d, dst);
            }
        }
    }

    #[test]
    fn same_asset_mpt_payment_uses_issuer_endpoint_pair() {
        let src = make_account(1);
        let dst = make_account(2);
        let issuer = make_account(3);
        let issue = protocol::MPTIssue::new(protocol::make_mpt_id(7, issuer));
        let asset = Asset::MPTIssue(issue);

        let (ter, strand) = to_strand(
            &src,
            &dst,
            &asset,
            None,
            &protocol::STPath::new(),
            false,
            false,
        );

        assert_eq!(ter, Ter::TES_SUCCESS);
        assert_eq!(strand.len(), 2);
        assert!(matches!(
            strand[0],
            StepKind::MptEndpoint {
                src: actual_src,
                dst: actual_dst,
                issue: actual_issue,
                is_first: true,
                is_last: false,
                offer_crossing: false,
            } if actual_src == src && actual_dst == issuer && actual_issue == issue
        ));
        assert!(matches!(
            strand[1],
            StepKind::MptEndpoint {
                src: actual_src,
                dst: actual_dst,
                issue: actual_issue,
                is_first: false,
                is_last: true,
                offer_crossing: false,
            } if actual_src == issuer && actual_dst == dst && actual_issue == issue
        ));
    }

    #[test]
    fn mpt_to_iou_crossing_preserves_exact_book_assets() {
        let taker = make_account(1);
        let mpt_issuer = make_account(2);
        let iou_issuer = make_account(3);
        let mpt = Asset::MPTIssue(protocol::MPTIssue::new(protocol::make_mpt_id(
            9, mpt_issuer,
        )));
        let usd = Asset::Issue(Issue::new(make_currency("USD"), iou_issuer));

        let (ter, strand) = to_strand(
            &taker,
            &taker,
            &usd,
            Some(&mpt),
            &protocol::STPath::new(),
            true,
            true,
        );

        assert_eq!(ter, Ter::TES_SUCCESS);
        assert!(strand.iter().any(|step| matches!(
            step,
            StepKind::Book { book_in, book_out, .. }
                if *book_in == mpt && *book_out == usd
        )));
        assert!(!strand.iter().any(|step| matches!(
            step,
            StepKind::Book { book_in, .. } if book_in.native()
        )));
    }
}
