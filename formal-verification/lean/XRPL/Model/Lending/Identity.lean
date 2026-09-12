import XRPL.Model.Protocol.TER

/-! Stable model identities for XLS-66 state.  The base protocol model has no
serialized account/issue records, so these fixed-width keys are the canonical
FFI representation: they are never synthesized by a transition. -/
namespace XRPL.Model.Lending

open XRPL.Model.Protocol

structure AccountId where value : UInt64 deriving DecidableEq, Repr, BEq
structure ObjectId where value : UInt64 deriving DecidableEq, Repr, BEq
structure IssueId where
  currency : UInt64
  issuer : AccountId
  deriving DecidableEq, Repr, BEq
structure CredentialAuth where
  counterpartySigned : Bool
  depositAuthorized : Bool
  credentialAuthorized : Bool
  deriving DecidableEq, Repr, BEq
structure LendingConfig where
  lendingEnabled : Bool
  singleAssetVaultEnabled : Bool
  maximumPaymentsPerTransaction : UInt32
  deriving DecidableEq, Repr, BEq
structure TransactionMetadata where
  transactionId : ObjectId
  sequence : UInt32
  ledgerCloseTime : UInt32
  deriving DecidableEq, Repr, BEq
structure VaultIdentity where
  vaultId : ObjectId
  owner : AccountId
  account : AccountId
  issue : IssueId
  config : LendingConfig
  metadata : TransactionMetadata
  deriving DecidableEq, Repr, BEq
structure BrokerIdentity where
  brokerId : ObjectId
  vaultId : ObjectId
  owner : AccountId
  account : AccountId
  deriving DecidableEq, Repr, BEq
structure LoanIdentity where
  loanId : ObjectId
  brokerId : ObjectId
  borrower : AccountId
  counterparty : AccountId
  issue : IssueId
  authorization : CredentialAuth
  metadata : TransactionMetadata
  deriving DecidableEq, Repr, BEq

def AccountId.valid (a : AccountId) : Bool := a.value != 0
def ObjectId.valid (o : ObjectId) : Bool := o.value != 0
def IssueId.valid (i : IssueId) : Bool := i.currency != 0 && i.issuer.valid

def VaultIdentity.wellFormed (v : VaultIdentity) : Bool :=
  v.vaultId.valid && v.owner.valid && v.account.valid && v.issue.valid &&
    v.config.lendingEnabled && v.config.singleAssetVaultEnabled &&
    v.config.maximumPaymentsPerTransaction != 0 && v.metadata.transactionId.valid

def BrokerIdentity.wellFormed (b : BrokerIdentity) : Bool :=
  b.brokerId.valid && b.vaultId.valid && b.owner.valid && b.account.valid

def LoanIdentity.wellFormed (l : LoanIdentity) : Bool :=
  l.loanId.valid && l.brokerId.valid && l.borrower.valid && l.counterparty.valid &&
    l.issue.valid && l.authorization.credentialAuthorized &&
    l.authorization.depositAuthorized && l.metadata.transactionId.valid

def LendingIdentity.valid (vault : VaultIdentity) (broker : BrokerIdentity) (loan : LoanIdentity) : TER :=
  if !vault.wellFormed || !broker.wellFormed || !loan.wellFormed then .temINVALID
  else if vault.vaultId != broker.vaultId || broker.brokerId != loan.brokerId || vault.issue != loan.issue then .temINVALID
  else .tesSUCCESS

end XRPL.Model.Lending
