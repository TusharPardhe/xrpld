//! Rust ledger view surfaces mirroring the current `ReadView.*` / `View.*`
//! roles while keeping explicit error seams.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;
use std::sync::Arc;

use basics::base_uint::Uint256;
use basics::chrono::NetClockTimePoint;
use protocol::{
    AccountID, Amendments, Keylet, LedgerEntryBase, LedgerEntryType, MPTAmount, MPTIssue, Rules,
    STAmount, STLedgerEntry, STObject, STTx, XRPAmount, amendments_keylet, get_field_by_symbol,
    sf_generic, skip_keylet, skip_keylet_for_ledger,
};
use shamap::mutation::MutationError;
use shamap::traversal::TraversalError;

use crate::{Fees, Ledger, LedgerHeader, LedgerTxReadError, SHAMapHash};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadViewTx {
    tx: Arc<STTx>,
    metadata: Option<Arc<STObject>>,
}

impl ReadViewTx {
    pub fn new(tx: Arc<STTx>, metadata: Option<Arc<STObject>>) -> Self {
        Self { tx, metadata }
    }

    pub fn tx(&self) -> &Arc<STTx> {
        &self.tx
    }

    pub fn metadata(&self) -> Option<&Arc<STObject>> {
        self.metadata.as_ref()
    }

    pub fn into_parts(self) -> (Arc<STTx>, Option<Arc<STObject>>) {
        (self.tx, self.metadata)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewError {
    Traversal(TraversalError),
    TxRead(LedgerTxReadError),
    Mutation(MutationError),
    DuplicateTx(Uint256),
    MissingMetadata(Uint256),
    InvalidFee(XRPAmount),
    Conversion(String),
}

impl From<TraversalError> for ViewError {
    fn from(value: TraversalError) -> Self {
        Self::Traversal(value)
    }
}

impl From<LedgerTxReadError> for ViewError {
    fn from(value: LedgerTxReadError) -> Self {
        Self::TxRead(value)
    }
}

impl From<MutationError> for ViewError {
    fn from(value: MutationError) -> Self {
        Self::Mutation(value)
    }
}

pub trait ReadView: Send + Sync + std::fmt::Debug {
    fn open(&self) -> bool;
    fn header(&self) -> LedgerHeader;
    fn fees(&self) -> Fees;
    fn rules(&self) -> Rules;
    fn exists(&self, keylet: Keylet) -> Result<bool, ViewError>;
    fn succ(&self, key: Uint256, last: Option<Uint256>) -> Result<Option<Uint256>, ViewError>;
    fn read(&self, keylet: Keylet) -> Result<Option<Arc<STLedgerEntry>>, ViewError>;
    fn sles(&self) -> Result<Vec<Arc<STLedgerEntry>>, ViewError>;
    fn tx_exists(&self, key: Uint256) -> Result<bool, ViewError>;
    fn tx_read(&self, key: Uint256) -> Result<Option<ReadViewTx>, ViewError>;
    fn txs(&self) -> Result<Vec<ReadViewTx>, ViewError>;

    fn parent_close_time(&self) -> NetClockTimePoint {
        self.header().parent_close_time.into()
    }

    fn seq(&self) -> u32 {
        self.header().seq
    }

    fn balance_hook_iou(
        &self,
        _account: AccountID,
        _issuer: AccountID,
        amount: STAmount,
    ) -> STAmount {
        amount
    }

    fn balance_hook_mpt(&self, _account: AccountID, issue: MPTIssue, amount: i64) -> STAmount {
        STAmount::from_mpt_amount(sf_generic(), MPTAmount::from_value(amount), issue)
    }

    fn balance_hook_self_issue_mpt(&self, issue: MPTIssue, amount: i64) -> STAmount {
        STAmount::from_mpt_amount(sf_generic(), MPTAmount::from_value(amount), issue)
    }

    fn owner_count_hook(
        &self,
        _account: AccountID,
        count: crate::OwnerCounts,
    ) -> crate::OwnerCounts {
        count
    }
}

pub trait DigestAwareReadView: ReadView {
    fn digest(&self, key: Uint256) -> Result<Option<Uint256>, ViewError>;
}

pub trait TypedReadViewExt: ReadView {
    fn read_typed<T, F>(&self, keylet: Keylet, map: F) -> Result<Option<T>, ViewError>
    where
        F: FnOnce(Arc<STLedgerEntry>) -> Result<T, String>,
    {
        self.read(keylet)?
            .map(map)
            .transpose()
            .map_err(ViewError::Conversion)
    }

    fn read_typed_wrapper<T>(&self, keylet: Keylet) -> Result<Option<T>, ViewError>
    where
        T: TryFrom<Arc<STLedgerEntry>, Error = String>,
    {
        self.read_typed(keylet, T::try_from)
    }
}

impl<T> TypedReadViewExt for T where T: ReadView + ?Sized {}

pub trait TypedLedgerEntryRef: Deref<Target = LedgerEntryBase> {}

impl<T> TypedLedgerEntryRef for T where T: Deref<Target = LedgerEntryBase> {}

impl ReadView for Ledger {
    fn open(&self) -> bool {
        false
    }

    fn header(&self) -> LedgerHeader {
        self.header()
    }

    fn fees(&self) -> Fees {
        self.fees()
    }

    fn rules(&self) -> Rules {
        self.rules().clone()
    }

    fn exists(&self, keylet: Keylet) -> Result<bool, ViewError> {
        Ok(self.exists_keylet(keylet)?)
    }

    fn succ(&self, key: Uint256, last: Option<Uint256>) -> Result<Option<Uint256>, ViewError> {
        Ok(self.succ(key, last)?)
    }

    fn read(&self, keylet: Keylet) -> Result<Option<Arc<STLedgerEntry>>, ViewError> {
        Ok(self.read(keylet)?.map(Arc::new))
    }

    fn sles(&self) -> Result<Vec<Arc<STLedgerEntry>>, ViewError> {
        let mut current = Uint256::zero();
        let mut result = Vec::new();

        while let Some(next) = self.succ(current, None)? {
            let keylet = Keylet::new(LedgerEntryType::Any, next);
            if let Some(sle) = self.read(keylet)? {
                result.push(Arc::new(sle));
            }
            current = next;
        }

        Ok(result)
    }

    fn tx_exists(&self, key: Uint256) -> Result<bool, ViewError> {
        self.try_tx_exists(key).map_err(ViewError::from)
    }

    fn tx_read(&self, key: Uint256) -> Result<Option<ReadViewTx>, ViewError> {
        Ok(self
            .tx_read(key)?
            .map(|(tx, meta)| ReadViewTx::new(tx, Some(Arc::new(meta.get_as_object())))))
    }

    fn txs(&self) -> Result<Vec<ReadViewTx>, ViewError> {
        Ok(self
            .tx_snapshot()?
            .into_iter()
            .map(|(tx, meta)| ReadViewTx::new(tx, Some(Arc::new(meta.get_as_object()))))
            .collect())
    }
}

impl DigestAwareReadView for Ledger {
    fn digest(&self, key: Uint256) -> Result<Option<Uint256>, ViewError> {
        Ok(self.digest(key)?)
    }
}

pub fn has_expired(view: &impl ReadView, exp: Option<u32>) -> bool {
    exp.is_some_and(|expiry| {
        crate::domain::lending_adapter::lossless::has_expired(
            view.parent_close_time().as_seconds(),
            expiry,
            false,
        )
    })
}

pub fn view_get_enabled_amendments(view: &impl ReadView) -> Result<BTreeSet<Uint256>, ViewError> {
    let Some(sle) = view.read(amendments_keylet())? else {
        return Ok(BTreeSet::new());
    };
    let wrapper = Amendments::new(sle).map_err(ViewError::Conversion)?;
    Ok(wrapper
        .get_amendments()
        .map(|vector| vector.value().iter().copied().collect())
        .unwrap_or_default())
}

pub fn view_get_majority_amendments(
    view: &impl ReadView,
) -> Result<BTreeMap<Uint256, NetClockTimePoint>, ViewError> {
    let Some(sle) = view.read(amendments_keylet())? else {
        return Ok(BTreeMap::new());
    };
    let wrapper = Amendments::new(sle).map_err(ViewError::Conversion)?;
    let Some(majorities) = wrapper.get_majorities() else {
        return Ok(BTreeMap::new());
    };

    Ok(majorities
        .iter()
        .map(|majority| {
            (
                majority.get_field_h256(get_field_by_symbol("sfAmendment")),
                NetClockTimePoint::from(majority.get_field_u32(get_field_by_symbol("sfCloseTime"))),
            )
        })
        .collect())
}

pub fn view_hash_of_seq(view: &impl ReadView, seq: u32) -> Result<Option<SHAMapHash>, ViewError> {
    let header = view.header();
    if seq > header.seq {
        return Ok(None);
    }
    if seq == header.seq {
        return Ok(Some(header.hash));
    }
    if seq + 1 == header.seq {
        return Ok(Some(header.parent_hash));
    }

    let diff = header.seq - seq;
    if diff <= 256
        && let Some(hash_index) = view.read(skip_keylet())?
    {
        let hashes = hash_index.get_field_v256(get_field_by_symbol("sfHashes"));
        if hashes.value().len() >= diff as usize {
            return Ok(Some(SHAMapHash::new(
                hashes.value()[hashes.value().len() - diff as usize],
            )));
        }
    }

    if (seq & 0xff) != 0 {
        return Ok(None);
    }

    let Some(hash_index) = view.read(skip_keylet_for_ledger(seq))? else {
        return Ok(None);
    };
    let last_seq = hash_index.get_field_u32(get_field_by_symbol("sfLastLedgerSequence"));
    let diff = (last_seq - seq) >> 8;
    let hashes = hash_index.get_field_v256(get_field_by_symbol("sfHashes"));
    if hashes.value().len() > diff as usize {
        return Ok(Some(SHAMapHash::new(
            hashes.value()[hashes.value().len() - diff as usize - 1],
        )));
    }
    Ok(None)
}

pub fn make_rules_given_ledger(
    ledger: &impl DigestAwareReadView,
    current: &Rules,
) -> Result<Rules, ViewError> {
    let keylet = amendments_keylet();
    let Some(digest) = ledger.digest(keylet.key)? else {
        return Ok(Rules::new(current.presets()));
    };
    let Some(sle) = ledger.read(keylet)? else {
        return Ok(Rules::new(current.presets()));
    };
    let amendments = sle
        .is_field_present(get_field_by_symbol("sfAmendments"))
        .then(|| sle.get_field_v256(get_field_by_symbol("sfAmendments")))
        .map(|field| field.value().to_vec())
        .unwrap_or_default();
    Ok(Rules::from_ledger(current.presets(), digest, amendments))
}

pub fn compatibility_reason(
    valid_ledger: &impl ReadView,
    test_ledger: &impl ReadView,
) -> Result<Option<String>, ViewError> {
    let valid = valid_ledger.header();
    let test = test_ledger.header();

    if valid.seq < test.seq {
        if let Some(hash) = view_hash_of_seq(test_ledger, valid.seq)?
            && hash != valid.hash
        {
            return Ok(Some(format!(
                "following ledger mismatch: expected {} at seq {}, got {}",
                valid.hash, valid.seq, hash
            )));
        }
    } else if valid.seq > test.seq {
        if let Some(hash) = view_hash_of_seq(valid_ledger, test.seq)?
            && hash != test.hash
        {
            return Ok(Some(format!(
                "preceding ledger mismatch: expected {} at seq {}, got {}",
                test.hash, test.seq, hash
            )));
        }
    } else if valid.hash != test.hash {
        return Ok(Some(format!(
            "same sequence {} but different hashes: {} vs {}",
            valid.seq, valid.hash, test.hash
        )));
    }

    Ok(None)
}

pub fn are_compatible(
    valid_ledger: &impl ReadView,
    test_ledger: &impl ReadView,
) -> Result<bool, ViewError> {
    Ok(compatibility_reason(valid_ledger, test_ledger)?.is_none())
}

pub fn after(now: NetClockTimePoint, mark: u32) -> bool {
    now.as_seconds() > mark
}
