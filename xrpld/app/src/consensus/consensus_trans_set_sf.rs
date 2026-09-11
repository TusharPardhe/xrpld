//! ConsensusTransSetSF — SHAMapSyncFilter for tx-set acquisition.
//!
//! Matches rippled's `ConsensusTransSetSF`: when downloading a peer's tx-set
//! via SHAMap sync, this filter checks if we already have each transaction
//! locally (in TransactionMaster's cache). If yes, it returns the serialized
//! node data directly — avoiding a network round-trip for that node.
//!
//! This is the KEY optimization for fast dispute resolution: when two tx-sets
//! differ by only 3 transactions out of 75, the filter supplies 72 of them
//! locally, reducing the download from 10+ round-trips to 1-2.

use std::sync::{Arc, RwLock, Weak};

use basics::blob::Blob;
use basics::sha_map_hash::SHAMapHash;
use protocol::{STTx, SerialIter};
use shamap::fetch::SHAMapSyncFilter;
use shamap::tree_node::SHAMapNodeType;

use crate::state::app_registry::AppTempNodeCache;
use crate::tx_queue::transaction_master::TransactionMaster;
use ledger::transaction_acquire::TransactionAcquireFilterFactory;

/// The hash prefix for TransactionNm leaves: 'T','X','N',0 = 0x54584E00
const HASH_PREFIX_TRANSACTION_ID: u32 = 0x54584E00;

type SubmitFetchedTransaction = Arc<dyn Fn(Arc<STTx>) + Send + Sync + 'static>;

/// Lifecycle-owned handoff from the acquisition filter to NetworkOPs.
///
/// The factory keeps only a `Weak` reference, so an in-flight acquisition can
/// never keep ApplicationRoot alive. ApplicationRoot installs the callback
/// after NetworkOPs is bound and disables it from StopTree during shutdown.
#[derive(Default)]
pub struct ConsensusFetchedTxSubmitAdapter {
    submit: RwLock<Option<SubmitFetchedTransaction>>,
}

impl ConsensusFetchedTxSubmitAdapter {
    pub(crate) fn install(&self, submit: SubmitFetchedTransaction) {
        *self
            .submit
            .write()
            .expect("consensus fetched transaction submit lock poisoned") = Some(submit);
    }

    pub fn disable(&self) {
        self.submit
            .write()
            .expect("consensus fetched transaction submit lock poisoned")
            .take();
    }

    #[cfg(test)]
    pub(crate) fn is_enabled(&self) -> bool {
        self.submit
            .read()
            .expect("consensus fetched transaction submit lock poisoned")
            .is_some()
    }

    fn submit(&self, tx: Arc<STTx>) -> bool {
        let submit = self
            .submit
            .read()
            .expect("consensus fetched transaction submit lock poisoned");
        submit.as_ref().is_some_and(|submit| {
            submit(tx);
            true
        })
    }
}

/// Factory that creates ConsensusTransSetSF instances.
/// Stored in InboundTransactions and cloned for each new acquisition.
pub struct ConsensusTransSetSFFactory {
    transaction_master: Arc<TransactionMaster>,
    node_cache: AppTempNodeCache,
    submit_adapter: Weak<ConsensusFetchedTxSubmitAdapter>,
}

impl ConsensusTransSetSFFactory {
    pub fn new(
        transaction_master: Arc<TransactionMaster>,
        node_cache: AppTempNodeCache,
        submit_adapter: Weak<ConsensusFetchedTxSubmitAdapter>,
    ) -> Self {
        Self {
            transaction_master,
            node_cache,
            submit_adapter,
        }
    }
}

impl TransactionAcquireFilterFactory for ConsensusTransSetSFFactory {
    fn build_filter(&self) -> Box<dyn SHAMapSyncFilter> {
        Box::new(ConsensusTransSetSF {
            transaction_master: Arc::clone(&self.transaction_master),
            node_cache: Arc::clone(&self.node_cache),
            submit_adapter: self.submit_adapter.clone(),
        })
    }
}

/// The actual filter used during SHAMap sync for tx-set acquisition.
struct ConsensusTransSetSF {
    transaction_master: Arc<TransactionMaster>,
    node_cache: AppTempNodeCache,
    submit_adapter: Weak<ConsensusFetchedTxSubmitAdapter>,
}

impl SHAMapSyncFilter for ConsensusTransSetSF {
    fn got_node(
        &mut self,
        from_filter: bool,
        node_hash: SHAMapHash,
        _ledger_seq: u32,
        node_data: Blob,
        node_type: SHAMapNodeType,
    ) {
        // `ConsensusTransSetSF::gotNode` ignores a node supplied by its own
        // filter. Cache the peer's original prefix-format bytes before any
        // transaction decoding. This matches rippled's NodeCache and lets a
        // competing acquisition reuse the exact network blob.
        if from_filter {
            return;
        }

        let _ = self
            .node_cache
            .insert(*node_hash.as_uint256(), node_data.clone());

        if node_type != SHAMapNodeType::TransactionNm || node_data.len() <= 16 {
            return;
        }

        // A prefixed TransactionNm is HashPrefix::TransactionId followed by
        // the canonical STTx bytes. rippled submits this transaction through
        // NetworkOPs. Do not insert it into TransactionMaster here: pinned
        // rippled only canonicalizes there after submitTransaction's validity
        // gate and preprocess stage. TempNodeCache above already owns exact
        // acquisition reuse, including invalid-signature transactions.
        let mut serial = SerialIter::new(&node_data[4..]);
        let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            STTx::from_serial_iter(&mut serial)
        }));
        let Ok(tx) = parsed else {
            return;
        };
        if tx.get_transaction_id() != *node_hash.as_uint256() {
            return;
        }
        let tx = Arc::new(tx);
        if let Some(submit_adapter) = self.submit_adapter.upgrade() {
            let _ = submit_adapter.submit(tx);
        }
    }

    fn get_node(&mut self, node_hash: SHAMapHash) -> Option<Blob> {
        // rippled checks TempNodeCache before TransactionMaster. This covers
        // inner nodes and non-transaction leaves learned while acquiring a
        // competing set, not only locally submitted transaction leaves.
        if let Some(node_data) = self.node_cache.retrieve(node_hash.as_uint256()) {
            return Some(node_data);
        }

        // The node_hash for TransactionNm leaves equals the transaction ID.
        // Check if we already have this transaction in our local cache.
        let tx_id = node_hash.as_uint256();
        let tx = self.transaction_master.fetch_from_cache(tx_id)?;
        let tx_guard = tx.lock().expect("transaction lock");
        let st_tx = tx_guard.get_s_transaction();

        // Serialize in "prefix format" matching SHAMap's serialize_with_prefix
        // for TransactionNm leaves: HASH_PREFIX_TRANSACTION_ID || serialized_stx
        let serialized = protocol::serialize_blob(st_tx.as_ref());
        let mut bytes = Vec::with_capacity(4 + serialized.len());
        bytes.extend_from_slice(&HASH_PREFIX_TRANSACTION_ID.to_be_bytes());
        bytes.extend_from_slice(&serialized);
        Some(bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol::{STAmount, TxType, get_field_by_symbol, serialize_blob};
    use shamap::tree_node::SHAMapTreeNode;
    use time::Duration;

    use crate::tx_queue::transaction::Transaction;

    fn payment() -> Arc<STTx> {
        Arc::new(STTx::new(TxType::PAYMENT, |tx| {
            tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
            tx.set_field_amount(
                get_field_by_symbol("sfAmount"),
                STAmount::new_native(1, false),
            );
            tx.set_field_amount(
                get_field_by_symbol("sfFee"),
                STAmount::new_native(10, false),
            );
        }))
    }

    fn factory() -> (
        ConsensusTransSetSFFactory,
        Arc<ConsensusFetchedTxSubmitAdapter>,
    ) {
        let submit_adapter = Arc::new(ConsensusFetchedTxSubmitAdapter::default());
        let factory = ConsensusTransSetSFFactory::new(
            Arc::new(TransactionMaster::new()),
            Arc::new(basics::tagged_cache::TaggedCache::new(
                "consensus-trans-set-filter",
                32,
                Duration::minutes(1),
                basics::tagged_cache::MonotonicClock::default(),
            )),
            Arc::downgrade(&submit_adapter),
        );
        (factory, submit_adapter)
    }

    #[test]
    fn cached_transaction_is_returned_in_exact_prefixed_shamap_format() {
        let (factory, _) = factory();
        let tx = payment();
        let tx_id = tx.get_transaction_id();
        let mut cached = Arc::new(std::sync::Mutex::new(Transaction::new(Arc::clone(&tx))));
        factory.transaction_master.canonicalize(&mut cached);

        let mut filter = factory.build_filter();
        let blob = filter
            .get_node(SHAMapHash::new(tx_id))
            .expect("cached transaction should satisfy the filter");
        let node = SHAMapTreeNode::make_from_prefix(&blob, SHAMapHash::new(tx_id))
            .expect("filter bytes must be a valid prefix-format SHAMap leaf");

        assert_eq!(node.get_type(), SHAMapNodeType::TransactionNm);
        assert_eq!(node.get_hash().as_uint256(), &tx_id);
        assert_eq!(
            node.peek_item().expect("leaf item").data(),
            serialize_blob(tx.as_ref())
        );
    }

    #[test]
    fn network_transaction_nodes_are_cached_for_later_filter_hits() {
        let (factory, submit_adapter) = factory();
        let tx = payment();
        let tx_id = tx.get_transaction_id();
        let submitted = Arc::new(std::sync::Mutex::new(Vec::new()));
        let submitted_capture = Arc::clone(&submitted);
        submit_adapter.install(Arc::new(move |tx| {
            submitted_capture
                .lock()
                .expect("submitted transaction lock")
                .push(tx.get_transaction_id());
        }));
        let mut prefixed = HASH_PREFIX_TRANSACTION_ID.to_be_bytes().to_vec();
        prefixed.extend_from_slice(&serialize_blob(tx.as_ref()));

        let mut filter = factory.build_filter();
        filter.got_node(
            false,
            SHAMapHash::new(tx_id),
            1,
            prefixed.clone(),
            SHAMapNodeType::TransactionNm,
        );

        assert!(
            factory
                .transaction_master
                .fetch_from_cache(&tx_id)
                .is_none()
        );
        assert_eq!(
            filter.get_node(SHAMapHash::new(tx_id)),
            Some(prefixed.clone())
        );
        assert_eq!(factory.node_cache.retrieve(&tx_id), Some(prefixed));
        assert_eq!(
            *submitted.lock().expect("submitted transaction lock"),
            vec![tx_id]
        );
    }

    #[test]
    fn known_filter_hits_do_not_resubmit_and_shutdown_disables_the_handoff() {
        let (factory, submit_adapter) = factory();
        let tx = payment();
        let tx_id = tx.get_transaction_id();
        let calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let call_capture = Arc::clone(&calls);
        submit_adapter.install(Arc::new(move |_| {
            call_capture.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }));
        let mut cached = Arc::new(std::sync::Mutex::new(Transaction::new(Arc::clone(&tx))));
        factory.transaction_master.canonicalize(&mut cached);

        let mut filter = factory.build_filter();
        let prefixed = filter
            .get_node(SHAMapHash::new(tx_id))
            .expect("known transaction filter hit");
        filter.got_node(
            true,
            SHAMapHash::new(tx_id),
            1,
            prefixed.clone(),
            SHAMapNodeType::TransactionNm,
        );
        assert_eq!(calls.load(std::sync::atomic::Ordering::Relaxed), 0);

        submit_adapter.disable();
        filter.got_node(
            false,
            SHAMapHash::new(tx_id),
            1,
            prefixed,
            SHAMapNodeType::TransactionNm,
        );
        assert_eq!(calls.load(std::sync::atomic::Ordering::Relaxed), 0);
    }

    #[test]
    fn temp_node_cache_returns_exact_non_transaction_bytes_and_preserves_first_duplicate() {
        let (factory, _) = factory();
        let hash = basics::base_uint::Uint256::from_array([0xAB; 32]);
        let original = vec![0xF0, 0x0D, 0xCA, 0xFE, 0x01];
        let duplicate = vec![0xDE, 0xAD, 0xBE, 0xEF];
        let mut filter = factory.build_filter();

        filter.got_node(
            false,
            SHAMapHash::new(hash),
            1,
            original.clone(),
            SHAMapNodeType::Inner,
        );
        filter.got_node(
            false,
            SHAMapHash::new(hash),
            1,
            duplicate,
            SHAMapNodeType::Inner,
        );

        assert_eq!(factory.node_cache.retrieve(&hash), Some(original.clone()));
        assert_eq!(filter.get_node(SHAMapHash::new(hash)), Some(original));
    }
}
