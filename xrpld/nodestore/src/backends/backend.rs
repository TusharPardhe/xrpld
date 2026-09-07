use crate::{Batch, NodeObject, Status};
use basics::base_uint::Uint256;
use std::sync::Arc;

pub trait Backend: Send + Sync + 'static {
    fn get_name(&self) -> String;

    fn get_block_size(&self) -> Option<usize> {
        None
    }

    fn open(&self, create_if_missing: bool) -> Result<(), String>;

    fn open_deterministic(
        &self,
        _create_if_missing: bool,
        _app_type: u64,
        _uid: u64,
        _salt: u64,
    ) -> Result<(), String> {
        Err(format!(
            "Deterministic appType/uid/salt not supported by backend {}",
            self.get_name()
        ))
    }

    fn is_open(&self) -> bool;

    fn close(&self) -> Result<(), String>;

    fn fetch(&self, hash: &Uint256) -> (Option<Arc<NodeObject>>, Status);

    /// Fast, conservative membership pre-check for a key.
    ///
    /// Returns `false` only when the backend can prove the key is absent (for
    /// example via a Bloom filter), allowing callers to skip an authoritative
    /// [`Backend::fetch`]. Returns `true` when the key might be present or when
    /// the backend has no membership index. The default is `true`, preserving
    /// existing behavior: callers must always perform the real fetch.
    ///
    /// A `false` result must never be returned for a stored key (no false
    /// negatives), so it is always safe to skip the fetch on `false`.
    fn may_contain(&self, _hash: &Uint256) -> bool {
        true
    }

    /// Evicts any in-memory membership filter (e.g. a Bloom filter) to reclaim
    /// RAM. Default is a no-op for backends without one. Called when a
    /// transient filter built to accelerate a bounded phase (such as history
    /// backfill) is no longer needed. Safe at any time: subsequent
    /// [`Backend::may_contain`] calls simply revert to `true` (must-check).
    fn evict_membership_filter(&self) {}

    fn fetch_batch(&self, hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status);

    /// Stores one object, reporting backend failures to the caller so it does
    /// not treat an unpersisted object as cacheable.
    fn store(&self, object: Arc<NodeObject>) -> Result<(), String>;

    fn store_batch(&self, batch: &Batch);

    /// Write a complete batch and report backend failures to the caller.
    ///
    /// `store_batch` remains for asynchronous legacy paths that cannot return
    /// a result. Snapshot and import paths must use this checked form so they
    /// never report a successful import after a failed durable write.
    fn store_batch_result(&self, batch: &Batch) -> Result<(), String> {
        for object in batch {
            self.store(Arc::clone(object))?;
        }
        Ok(())
    }

    fn sync(&self);

    /// Checked durability barrier. Backends without a fallible checkpoint keep
    /// the historical no-op/default behavior; NuDB overrides this to expose
    /// its active-burst commit and fsync failures to lifecycle owners.
    fn sync_result(&self) -> Result<(), String> {
        self.sync();
        Ok(())
    }

    /// Begin bulk import mode. Optimized for loading millions of nodes sequentially.
    /// Skips existence checks, disables burst checkpoints, pre-allocates structures.
    fn bulk_import_start(&self, _estimated_nodes: u64) -> Result<(), String> {
        Ok(())
    }

    /// Finish bulk import. Flushes all data to disk, builds indexes.
    fn bulk_import_finish(&self) -> Result<(), String> {
        Ok(())
    }

    /// Mark an import as failed after it has started. Backends with an
    /// incomplete-import marker must keep or restore that marker so an invalid
    /// post-finalization snapshot cannot be reopened as a successful import.
    fn bulk_import_abort(&self) {}

    fn for_each(&self, callback: &mut dyn FnMut(Arc<NodeObject>));

    /// Traverse all objects, reporting backend traversal failures to callers
    /// that need a complete view. The default preserves historical behavior
    /// for existing backends that only implement `for_each`.
    fn for_each_result(&self, callback: &mut dyn FnMut(Arc<NodeObject>)) -> Result<(), String> {
        self.for_each(callback);
        Ok(())
    }

    fn get_write_load(&self) -> i32;

    fn set_delete_path(&self);

    fn verify(&self) {}

    fn fd_required(&self) -> i32;
}
