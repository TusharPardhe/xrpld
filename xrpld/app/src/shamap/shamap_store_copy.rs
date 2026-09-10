use crate::shamap::shamap_store_component::SHAMapStoreComponentRuntime;
use crate::shamap::shamap_store_health::{
    SHAMapStoreHealthPolicy, SHAMapStoreHealthStatus, wait_for_health,
};
use crate::{
    SHAMapStoreCopyRuntime, SHAMapStoreNodeFamilyCacheRuntime, SHAMapStoreNodeStoreRuntime,
};
use basics::base_uint::Uint256;
use basics::memory::intrusive_pointer::SharedIntrusive;
use ledger::Ledger;
use shamap::traversal::TraversalError;
use shamap::tree_node::SHAMapTreeNode;
use std::sync::Arc;

pub const SHAMAP_STORE_COPY_CHECK_HEALTH_INTERVAL: u64 = 1000;
pub const SHAMAP_STORE_COPY_BATCH_SIZE: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SHAMapStoreCopyDisposition {
    Completed { node_count: u64 },
    Stopped { node_count: u64 },
    MissingNode { hash: Uint256, node_count: u64 },
}

#[derive(Debug, Default)]
pub struct ValidatedLedgerCopyRuntime;

fn copy_rotation_batch(
    pending: &mut Vec<SharedIntrusive<SHAMapTreeNode>>,
    node_store: &dyn SHAMapStoreNodeStoreRuntime,
) -> Result<(), String> {
    let hashes = pending
        .iter()
        .map(|node| *node.get_hash().as_uint256())
        .collect::<Vec<_>>();
    let (_copied, missing) = node_store.copy_to_writable_batch_detailed(&hashes)?;
    if !missing.is_empty() {
        let missing = missing
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        let mut rescue = Vec::with_capacity(missing.len());
        for node in pending.iter() {
            let hash = *node.get_hash().as_uint256();
            if missing.contains(&hash) {
                if node.cowid() != 0 {
                    return Err(
                        "validated SHAMap rotation rescue encountered a dirty node".to_owned()
                    );
                }
                let data = node
                    .serialize_with_prefix()
                    .map_err(|error| format!("serialize resident rotation node: {error:?}"))?;
                rescue.push((hash, data));
            }
        }
        if rescue.len() != missing.len() {
            return Err("resident rotation rescue lost a validated SHAMap node".to_owned());
        }
        tracing::warn!(
            target: "shamap_store",
            rescued_nodes = rescue.len(),
            "re-storing validated SHAMap nodes missing from both rotating backends"
        );
        node_store.store_account_nodes(rescue)?;
    }
    pending.clear();
    Ok(())
}

impl SHAMapStoreCopyRuntime for ValidatedLedgerCopyRuntime {
    fn copy_validated_ledger(
        &self,
        validated_ledger: Arc<Ledger>,
        node_family: &dyn SHAMapStoreNodeFamilyCacheRuntime,
        node_store: &dyn SHAMapStoreNodeStoreRuntime,
        runtime: &mut dyn SHAMapStoreComponentRuntime,
        health_policy: SHAMapStoreHealthPolicy,
    ) -> Result<SHAMapStoreCopyDisposition, String> {
        copy_validated_state_map(
            validated_ledger,
            node_family,
            node_store,
            runtime,
            health_policy,
        )
    }
}

pub fn copy_validated_state_map(
    validated_ledger: Arc<Ledger>,
    node_family: &dyn SHAMapStoreNodeFamilyCacheRuntime,
    node_store: &dyn SHAMapStoreNodeStoreRuntime,
    runtime: &mut dyn SHAMapStoreComponentRuntime,
    health_policy: SHAMapStoreHealthPolicy,
) -> Result<SHAMapStoreCopyDisposition, String> {
    let mut node_count = 0u64;
    let mut stopped = false;
    let mut copy_error = None;
    let mut pending: Vec<SharedIntrusive<SHAMapTreeNode>> =
        Vec::with_capacity(SHAMAP_STORE_COPY_BATCH_SIZE);
    let visit_result = node_family.visit_state_map_nodes(validated_ledger.as_ref(), &mut |node| {
        pending.push(node.clone());
        node_count += 1;

        if pending.len() == SHAMAP_STORE_COPY_BATCH_SIZE
            && let Err(error) = copy_rotation_batch(&mut pending, node_store)
        {
            copy_error = Some(error);
            return false;
        }

        if !node_count.is_multiple_of(SHAMAP_STORE_COPY_CHECK_HEALTH_INTERVAL) {
            return true;
        }

        let keep_going = wait_for_health(&health_policy, runtime, |runtime, duration| {
            runtime.sleep(duration);
        }) != SHAMapStoreHealthStatus::Stopping;
        stopped = !keep_going;
        keep_going
    });

    if let Some(error) = copy_error {
        return Err(error);
    }
    if !pending.is_empty() {
        copy_rotation_batch(&mut pending, node_store)?;
    }

    match visit_result {
        Ok(()) if stopped => Ok(SHAMapStoreCopyDisposition::Stopped { node_count }),
        Ok(()) => Ok(SHAMapStoreCopyDisposition::Completed { node_count }),
        Err(TraversalError::MissingNode(hash)) => Ok(SHAMapStoreCopyDisposition::MissingNode {
            hash: *hash.as_uint256(),
            node_count,
        }),
        Err(e) => Err(format!("Traversal error: {:?}", e)),
    }
}

#[cfg(test)]
mod tests {
    use super::copy_rotation_batch;
    use crate::SHAMapStoreNodeStoreRuntime;
    use basics::base_uint::Uint256;
    use basics::blob::Blob;
    use nodestore::Backend;
    use shamap::item::SHAMapItem;
    use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use std::sync::Mutex;

    #[derive(Default)]
    struct MissingBackends {
        stored: Mutex<Vec<(Uint256, Blob)>>,
        fail_store: bool,
    }

    impl SHAMapStoreNodeStoreRuntime for MissingBackends {
        fn fetch_node_object(&self, _hash: &Uint256, _ledger_seq: u32) -> bool {
            false
        }

        fn copy_to_writable_batch_detailed(
            &self,
            hashes: &[Uint256],
        ) -> Result<(usize, Vec<Uint256>), String> {
            Ok((0, hashes.to_vec()))
        }

        fn store_account_nodes(&self, nodes: Vec<(Uint256, Blob)>) -> Result<(), String> {
            if self.fail_store {
                return Err("injected resident rescue write failure".to_owned());
            }
            self.stored.lock().expect("stored nodes lock").extend(nodes);
            Ok(())
        }

        fn rotate_with(&self, _new_backend: Box<dyn Backend>) -> (String, String) {
            unreachable!("rotation is outside this batch-level regression")
        }
    }

    #[test]
    fn resident_validated_node_missing_from_both_backends_is_restored() {
        let node = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0x51; 32]), vec![0xA5; 48]),
            0,
        );
        let hash = *node.get_hash().as_uint256();
        let expected = node.serialize_with_prefix().expect("serialize node");
        let mut pending = vec![node];
        let store = MissingBackends::default();

        copy_rotation_batch(&mut pending, &store).expect("resident rescue");

        assert!(pending.is_empty());
        assert_eq!(
            *store.stored.lock().expect("stored nodes lock"),
            vec![(hash, expected)]
        );
    }

    #[test]
    fn dirty_resident_node_is_never_used_for_rotation_rescue() {
        let node = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0x52; 32]), vec![0xA6; 48]),
            1,
        );
        let mut pending = vec![node];
        let error = copy_rotation_batch(&mut pending, &MissingBackends::default())
            .expect_err("dirty node must fail rescue");
        assert!(error.contains("dirty node"));
    }

    #[test]
    fn resident_rescue_write_failure_aborts_rotation_copy() {
        let node = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([0x53; 32]), vec![0xA7; 48]),
            0,
        );
        let mut pending = vec![node];
        let store = MissingBackends {
            fail_store: true,
            ..MissingBackends::default()
        };
        assert_eq!(
            copy_rotation_batch(&mut pending, &store),
            Err("injected resident rescue write failure".to_owned())
        );
    }
}
