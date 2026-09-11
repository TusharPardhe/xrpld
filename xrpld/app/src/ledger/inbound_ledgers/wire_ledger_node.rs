//! Wire normalization for `TMLedgerNode` references.
//!
//! This mirrors rippled `LedgerNodeHelpers.cpp::getSHAMapNodeID`: legacy
//! `nodeid` is accepted for either node kind (with a leaf-key consistency
//! check); modern `id` identifies only inner nodes; modern `depth` identifies
//! only leaves and is reconstructed from the decoded leaf key. Base replies
//! carry no node reference at all. Their slot zero is a raw ledger header;
//! their optional slots one and two are SHAMap network-wire roots, matching
//! rippled `PeerImp::sendLedgerBase` and `SHAMap::serializeRoot`.

use ledger::{InboundLedgerDataType, InboundLedgerNodeData};
use overlay::message::wire::{TmLedgerNode, tm_ledger_node};
use shamap::node_id::{SHAMAP_LEAF_DEPTH, SHAMapNodeId, deserialize_shamap_node_id};
use shamap::tree_node::SHAMapTreeNode;

/// Decode one wire node and canonicalize its reference into the legacy
/// serialized `SHAMapNodeId` representation consumed by `InboundLedger`.
///
/// References are deliberately validated against the decoded SHAMap node,
/// rather than trusting the sender's field shape. This preserves rippled's
/// malformed-packet rejection while allowing peers that negotiated
/// `LedgerNodeDepth` to send valid `id` / `depth` replies.
pub(crate) fn decode_wire_ledger_node(
    node: &TmLedgerNode,
    packet_type: InboundLedgerDataType,
    packet_index: usize,
) -> Option<InboundLedgerNodeData> {
    if node.nodedata.is_empty() {
        return None;
    }

    let has_modern_reference = node.reference.is_some();
    if packet_type == InboundLedgerDataType::Base {
        // rippled `PeerImp::sendLedgerBase` emits a raw LedgerHeader in slot
        // zero and `SHAMap::serializeRoot` network-wire roots in slots one and
        // two. Base payloads never carry node references. Validate the two
        // root slots with the same `makeFromWire` contract used by rippled
        // `InboundLedger::takeAsRootNode`, but preserve their exact wire bytes.
        if node.nodeid.is_some() || has_modern_reference {
            return None;
        }
        if (1..=2).contains(&packet_index)
            && SHAMapTreeNode::make_from_wire(&node.nodedata)
                .ok()?
                .is_none()
        {
            return None;
        }
        return Some(InboundLedgerNodeData::new(None, node.nodedata.clone()));
    }

    let decoded = SHAMapTreeNode::make_from_wire(&node.nodedata).ok()??;
    let node_id = match (&node.nodeid, &node.reference) {
        // Rippled explicitly rejects mixed legacy and protocol-2.3 fields.
        (Some(_), Some(_)) => return None,
        (Some(legacy), None) => {
            let node_id = deserialize_shamap_node_id(legacy)?;
            if decoded.is_leaf() {
                let key = decoded.peek_item()?.key();
                let expected = SHAMapNodeId::create_id(node_id.get_depth(), key).ok()?;
                if node_id.get_node_id() != expected.get_node_id() {
                    return None;
                }
            }
            legacy.clone()
        }
        (None, Some(tm_ledger_node::Reference::Id(id))) => {
            if !decoded.is_inner() || deserialize_shamap_node_id(id).is_none() {
                return None;
            }
            id.clone()
        }
        (None, Some(tm_ledger_node::Reference::Depth(depth))) => {
            if !decoded.is_leaf() || (*depth as usize) > SHAMAP_LEAF_DEPTH {
                return None;
            }
            let key = decoded.peek_item()?.key();
            SHAMapNodeId::create_id(*depth as usize, key)
                .ok()?
                .get_raw_string()
        }
        (None, None) => return None,
    };

    Some(InboundLedgerNodeData::new(
        Some(node_id),
        node.nodedata.clone(),
    ))
}

#[cfg(test)]
mod tests {
    use super::decode_wire_ledger_node;
    use basics::base_uint::Uint256;
    use ledger::InboundLedgerDataType;
    use overlay::message::wire::{TmLedgerNode, tm_ledger_node};
    use shamap::node_id::SHAMapNodeId;
    use shamap::nodes::item::SHAMapItem;
    use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};

    fn inner_wire() -> Vec<u8> {
        let mut wire = vec![0; 16 * 32];
        wire.push(2);
        wire
    }

    fn leaf_wire(key: Uint256) -> Vec<u8> {
        SHAMapTreeNode::new_leaf(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(key, vec![0x10; 12]),
            0,
        )
        .serialize_for_wire()
        .expect("leaf serializes")
    }

    fn base_root_wire() -> Vec<u8> {
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(
            3,
            basics::sha_map_hash::SHAMapHash::new(Uint256::from(0x73)),
        );
        root.update_hash();
        root.serialize_for_wire().expect("root wire serializes")
    }

    #[test]
    fn accepts_ledger_node_depth_references_and_canonicalizes_leaves() {
        let inner_id = SHAMapNodeId::default().get_raw_string();
        let inner = decode_wire_ledger_node(
            &TmLedgerNode {
                nodedata: inner_wire(),
                reference: Some(tm_ledger_node::Reference::Id(inner_id.clone())),
                ..TmLedgerNode::default()
            },
            InboundLedgerDataType::StateNode,
            0,
        )
        .expect("modern inner id is valid");
        assert_eq!(inner.node_id, Some(inner_id));

        let leaf_wire = leaf_wire(Uint256::from_array([0xA5; 32]));
        let decoded_key = SHAMapTreeNode::make_from_wire(&leaf_wire)
            .expect("leaf wire decodes")
            .expect("leaf wire is non-empty")
            .peek_item()
            .expect("decoded node is a leaf")
            .key();
        let leaf = decode_wire_ledger_node(
            &TmLedgerNode {
                nodedata: leaf_wire,
                reference: Some(tm_ledger_node::Reference::Depth(7)),
                ..TmLedgerNode::default()
            },
            InboundLedgerDataType::TransactionNode,
            0,
        )
        .expect("modern leaf depth is valid");
        assert_eq!(
            leaf.node_id,
            Some(
                SHAMapNodeId::create_id(7, decoded_key)
                    .expect("depth is valid")
                    .get_raw_string()
            )
        );
    }

    #[test]
    fn rejects_invalid_or_ambiguous_ledger_node_references() {
        let legacy = SHAMapNodeId::default().get_raw_string();
        let invalid_cases = [
            TmLedgerNode {
                nodedata: inner_wire(),
                reference: Some(tm_ledger_node::Reference::Depth(1)),
                ..TmLedgerNode::default()
            },
            TmLedgerNode {
                nodedata: leaf_wire(Uint256::from_array([0xB6; 32])),
                reference: Some(tm_ledger_node::Reference::Id(legacy.clone())),
                ..TmLedgerNode::default()
            },
            TmLedgerNode {
                nodedata: inner_wire(),
                nodeid: Some(legacy),
                reference: Some(tm_ledger_node::Reference::Id(vec![0; 33])),
                ..TmLedgerNode::default()
            },
        ];
        for node in invalid_cases {
            assert!(
                decode_wire_ledger_node(&node, InboundLedgerDataType::StateNode, 0).is_none(),
                "invalid/mixed reference must be rejected"
            );
        }

        assert!(
            decode_wire_ledger_node(
                &TmLedgerNode {
                    nodedata: vec![0; 123],
                    nodeid: Some(vec![0; 33]),
                    ..TmLedgerNode::default()
                },
                InboundLedgerDataType::Base,
                0,
            )
            .is_none(),
            "Base packets cannot carry a node reference"
        );
    }

    #[test]
    fn preserves_raw_base_header_and_network_wire_roots() {
        let expected_wire = base_root_wire();
        let header = TmLedgerNode {
            nodedata: vec![0xAB; 123],
            ..TmLedgerNode::default()
        };
        let root = TmLedgerNode {
            nodedata: expected_wire.clone(),
            ..TmLedgerNode::default()
        };

        let decoded_header = decode_wire_ledger_node(&header, InboundLedgerDataType::Base, 0)
            .expect("raw Base header is preserved");
        assert_eq!(decoded_header.node_data, header.nodedata);

        let decoded_root = decode_wire_ledger_node(&root, InboundLedgerDataType::Base, 1)
            .expect("rippled Base state root is valid network wire");
        assert_eq!(decoded_root.node_id, None);
        assert_eq!(decoded_root.node_data, expected_wire);
        assert!(
            SHAMapTreeNode::make_from_wire(&decoded_root.node_data)
                .expect("root is valid network wire")
                .expect("root is non-empty")
                .is_inner()
        );
    }

    #[test]
    fn rejects_malformed_network_wire_data_in_a_base_root_slot() {
        assert!(
            decode_wire_ledger_node(
                &TmLedgerNode {
                    nodedata: vec![0xFF],
                    ..TmLedgerNode::default()
                },
                InboundLedgerDataType::Base,
                1,
            )
            .is_none()
        );
    }
}
