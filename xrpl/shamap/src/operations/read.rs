//! Current `SHAMap` direct read helpers.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::item::SHAMapItem;
use crate::search::{find_key, find_key_with_family};
use crate::traversal::TraversalError;
use crate::tree_node::SHAMapTreeNode;
use basics::base_uint::Uint256;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

pub fn has_item<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<bool, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    Ok(find_key(root, id, backed, fetch)?.is_some())
}

pub fn has_item_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<bool, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    Ok(find_key_with_family(root, id, backed, ledger_seq, family)?.is_some())
}

pub fn peek_item<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SHAMapItem>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    Ok(find_key(root, id, backed, fetch)?.and_then(|leaf| leaf.peek_item()))
}

pub fn peek_item_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<SHAMapItem>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    Ok(find_key_with_family(root, id, backed, ledger_seq, family)?
        .and_then(|leaf| leaf.peek_item()))
}

pub fn peek_item_with_hash<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<(SHAMapItem, SHAMapHash)>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    Ok(find_key(root, id, backed, fetch)?
        .and_then(|leaf| leaf.peek_item().map(|item| (item, leaf.get_hash()))))
}

pub fn peek_item_with_hash_and_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<(SHAMapItem, SHAMapHash)>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    Ok(find_key_with_family(root, id, backed, ledger_seq, family)?
        .and_then(|leaf| leaf.peek_item().map(|item| (item, leaf.get_hash()))))
}

#[cfg(test)]
mod tests {
    use super::{has_item, peek_item, peek_item_with_hash};
    use crate::item::SHAMapItem;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use basics::base_uint::Uint256;
    use basics::sha_map_hash::SHAMapHash;

    fn key(hex: &str) -> Uint256 {
        Uint256::from_hex(hex).expect("hex should parse")
    }

    fn sample_hash(fill: u8) -> SHAMapHash {
        SHAMapHash::new(Uint256::from_array([fill; 32]))
    }

    #[test]
    fn has_item_and_peek_item_match_exact_key_role() {
        let stored_key = key("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF");
        let missing_key = key("1F34567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF");
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(stored_key, vec![1; 12]),
            0,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, leaf.get_hash());
        root.share_child(1, &leaf);
        root.update_hash_deep();

        assert!(has_item(&root, stored_key, false, &mut |_| None).expect("lookup should succeed"));
        assert!(
            !has_item(&root, missing_key, false, &mut |_| None)
                .expect("missing lookup should succeed")
        );
        assert_eq!(
            peek_item(&root, stored_key, false, &mut |_| None).expect("peek should succeed"),
            Some(SHAMapItem::new(stored_key, vec![1; 12]))
        );
        assert_eq!(
            peek_item(&root, missing_key, false, &mut |_| None)
                .expect("missing peek should succeed"),
            None
        );
    }

    #[test]
    fn peek_item_with_hash_returns_leaf_hash_when_found() {
        let key = key("ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890");
        let expected_hash = sample_hash(0x77);
        let leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![2; 12]),
            0,
            expected_hash,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(10, expected_hash);
        root.share_child(10, &leaf);
        root.update_hash_deep();

        let resolved = peek_item_with_hash(&root, key, false, &mut |_| None)
            .expect("peek-with-hash should succeed")
            .expect("stored leaf should resolve");
        assert_eq!(resolved.0, SHAMapItem::new(key, vec![2; 12]));
        assert_eq!(resolved.1, expected_hash);
    }

    #[test]
    fn direct_read_helpers_can_fetch_backed_missing_children() {
        let key = key("2000000000000000000000000000000000000000000000000000000000000000");
        let expected_hash = sample_hash(0x55);
        let fetched_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![3; 12]),
            0,
            expected_hash,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(2, expected_hash);

        let mut fetch_calls = 0;
        let item = peek_item(&root, key, true, &mut |_| {
            fetch_calls += 1;
            Some(fetched_leaf.clone())
        })
        .expect("fetch-backed peek should succeed");

        assert_eq!(fetch_calls, 1);
        assert_eq!(item, Some(SHAMapItem::new(key, vec![3; 12])));
        assert!(root.get_child(2).is_some());
    }
}
