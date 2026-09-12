import XRPL.FFI.Lending.Wire.Primitive
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.LoanBroker.LoanBroker
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.FFI.Lending.Wire

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault

private def tagTER : TER → UInt8
  | .tesSUCCESS => 0 | .tecINTERNAL => 1 | .tecAMM_INVALID_TOKENS => 2 | .tecAMM_FAILED => 3
  | .tecUNFUNDED_AMM => 4 | .tecNO_ENTRY => 5 | .tecWRONG_ASSET => 6 | .tecOBJECT_NOT_FOUND => 7
  | .tecNO_AUTH => 8 | .tecINSUFFICIENT_RESERVE => 9 | .tecDIR_FULL => 10 | .tecNO_TARGET => 11
  | .tecEXPIRED => 12 | .tecNO_PERMISSION => 13 | .tecDUPLICATE => 14 | .tecNO_LINE_INSUF_RESERVE => 15
  | .tecHAS_OBLIGATIONS => 16 | .tecNO_DST => 17 | .tecDST_TAG_NEEDED => 18 | .tecNO_LINE => 19
  | .tecFAILED_PROCESSING => 20 | .tecPATH_DRY => 21 | .tecINSUFFICIENT_FUNDS => 22 | .tecKILLED => 23
  | .tefINTERNAL => 24 | .tefBAD_LEDGER => 25 | .terNO_ACCOUNT => 26 | .terNO_RIPPLE => 27
  | .tecFROZEN => 28 | .tecLOCKED => 29 | .temMALFORMED => 30 | .temBAD_AMOUNT => 31
  | .telFAILED_PROCESSING => 32 | .temINVALID => 33 | .temINVALID_FLAG => 34 | .temBAD_FEE => 35
  | .temBAD_SRC_ACCOUNT => 36 | .temDISABLED => 37 | .tecLIMIT_EXCEEDED => 38
  | .tecPRECISION_LOSS => 39 | .tecTOO_SOON => 40 | .tecINSUFFICIENT_PAYMENT => 41

private def untagTER (offset : Nat) : UInt8 → Except DecodeError TER
  | 0 => .ok .tesSUCCESS | 1 => .ok .tecINTERNAL | 2 => .ok .tecAMM_INVALID_TOKENS | 3 => .ok .tecAMM_FAILED
  | 4 => .ok .tecUNFUNDED_AMM | 5 => .ok .tecNO_ENTRY | 6 => .ok .tecWRONG_ASSET | 7 => .ok .tecOBJECT_NOT_FOUND
  | 8 => .ok .tecNO_AUTH | 9 => .ok .tecINSUFFICIENT_RESERVE | 10 => .ok .tecDIR_FULL | 11 => .ok .tecNO_TARGET
  | 12 => .ok .tecEXPIRED | 13 => .ok .tecNO_PERMISSION | 14 => .ok .tecDUPLICATE | 15 => .ok .tecNO_LINE_INSUF_RESERVE
  | 16 => .ok .tecHAS_OBLIGATIONS | 17 => .ok .tecNO_DST | 18 => .ok .tecDST_TAG_NEEDED | 19 => .ok .tecNO_LINE
  | 20 => .ok .tecFAILED_PROCESSING | 21 => .ok .tecPATH_DRY | 22 => .ok .tecINSUFFICIENT_FUNDS | 23 => .ok .tecKILLED
  | 24 => .ok .tefINTERNAL | 25 => .ok .tefBAD_LEDGER | 26 => .ok .terNO_ACCOUNT | 27 => .ok .terNO_RIPPLE
  | 28 => .ok .tecFROZEN | 29 => .ok .tecLOCKED | 30 => .ok .temMALFORMED | 31 => .ok .temBAD_AMOUNT
  | 32 => .ok .telFAILED_PROCESSING | 33 => .ok .temINVALID | 34 => .ok .temINVALID_FLAG | 35 => .ok .temBAD_FEE
  | 36 => .ok .temBAD_SRC_ACCOUNT | 37 => .ok .temDISABLED | 38 => .ok .tecLIMIT_EXCEEDED
  | 39 => .ok .tecPRECISION_LOSS | 40 => .ok .tecTOO_SOON | 41 => .ok .tecINSUFFICIENT_PAYMENT
  | value => .error (.nonCanonical offset)

def encodeTER (value : TER) : ByteArray := encodeU8 (tagTER value)
def readTER (c : Cursor) : Except DecodeError (TER × Cursor) := do
  let offset := c.offset
  let (tag, next) ← readU8 c
  pure (← untagTER offset tag, next)

def encodeError : Error → ByteArray
  | .overflow => one 0 | .divByZero => one 1 | .outOfRange => one 2
  | .normalize1 => one 3 | .normalize1_5 => one 4 | .normalize2 => one 5
  | .notComparable => one 6 | .cannotConvert => one 7 | .notLawful => one 8

def readError (c : Cursor) : Except DecodeError (Error × Cursor) := do
  let offset := c.offset
  let (tag, next) ← readU8 c
  let value ← match tag with
    | 0 => .ok .overflow | 1 => .ok .divByZero | 2 => .ok .outOfRange | 3 => .ok .normalize1
    | 4 => .ok .normalize1_5 | 5 => .ok .normalize2 | 6 => .ok .notComparable | 7 => .ok .cannotConvert
    | 8 => .ok .notLawful | _ => .error (.nonCanonical offset)
  pure (value, next)

def encodeVaultIdentity (x : VaultIdentity) : Except DecodeError ByteArray :=
  return (← encodeObjectId x.vaultId) ++ (← encodeAccountId x.owner) ++ (← encodeAccountId x.account) ++
    (← encodeIssueId x.issue) ++ (← encodeLendingConfig x.config) ++ (← encodeTransactionMetadata x.metadata)
def readVaultIdentity (c : Cursor) : Except DecodeError (VaultIdentity × Cursor) := do
  let (vaultId, c) ← readObjectId c; let (owner, c) ← readAccountId c; let (account, c) ← readAccountId c
  let (issue, c) ← readIssueId c; let (config, c) ← readLendingConfig c; let (metadata, c) ← readTransactionMetadata c
  pure ({ vaultId, owner, account, issue, config, metadata }, c)

def encodeBrokerIdentity (x : BrokerIdentity) : Except DecodeError ByteArray :=
  return (← encodeObjectId x.brokerId) ++ (← encodeObjectId x.vaultId) ++ (← encodeAccountId x.owner) ++ (← encodeAccountId x.account)
def readBrokerIdentity (c : Cursor) : Except DecodeError (BrokerIdentity × Cursor) := do
  let (brokerId, c) ← readObjectId c; let (vaultId, c) ← readObjectId c
  let (owner, c) ← readAccountId c; let (account, c) ← readAccountId c
  pure ({ brokerId, vaultId, owner, account }, c)

def encodeLoanIdentity (x : LoanIdentity) : Except DecodeError ByteArray :=
  return (← encodeObjectId x.loanId) ++ (← encodeObjectId x.brokerId) ++ (← encodeAccountId x.borrower) ++
    (← encodeAccountId x.counterparty) ++ (← encodeIssueId x.issue) ++ (← encodeCredentialAuth x.authorization) ++
    (← encodeTransactionMetadata x.metadata)
def readLoanIdentity (c : Cursor) : Except DecodeError (LoanIdentity × Cursor) := do
  let (loanId, c) ← readObjectId c; let (brokerId, c) ← readObjectId c; let (borrower, c) ← readAccountId c
  let (counterparty, c) ← readAccountId c; let (issue, c) ← readIssueId c; let (authorization, c) ← readCredentialAuth c
  let (metadata, c) ← readTransactionMetadata c
  pure ({ loanId, brokerId, borrower, counterparty, issue, authorization, metadata }, c)

def encodeRawVault (x : RawVault) : Except DecodeError ByteArray :=
  return (← encodeNumber x.assetsTotal) ++ (← encodeNumber x.assetsAvailable) ++ (← encodeNumber x.assetsReserved) ++
    (← encodeOption encodeNumber x.assetsMaximum) ++ (← encodeNumericType x.numericType) ++ encodeU8 x.scale ++
    (← encodeNumber x.sharesTotal) ++ (← encodeNumber x.lossUnrealized)
def readRawVault (c : Cursor) : Except DecodeError (RawVault × Cursor) := do
  let (assetsTotal, c) ← readNumber c; let (assetsAvailable, c) ← readNumber c; let (assetsReserved, c) ← readNumber c
  let (assetsMaximum, c) ← readOption readNumber c; let (numericType, c) ← readNumericType c; let (scale, c) ← readU8 c
  let (sharesTotal, c) ← readNumber c; let (lossUnrealized, c) ← readNumber c
  pure ({ assetsTotal, assetsAvailable, assetsReserved, assetsMaximum, numericType, scale, sharesTotal, lossUnrealized }, c)

def encodeVault (x : Vault) : Except DecodeError ByteArray := encodeRawVault x.toRawVault
def readVault (c : Cursor) : Except DecodeError (Vault × Cursor) := do
  let offset := c.offset
  let (raw, c) ← readRawVault c
  match raw.to_lawful with
  | .ok vault => pure (vault, c)
  | .error _ => .error (.nonCanonical offset)

def encodeLoanBroker (x : LoanBroker) : Except DecodeError ByteArray :=
  return (← encodeBrokerIdentity x.identity) ++ encodeU16 x.managementFeeRate ++ encodeU32 x.coverRateMinimum ++
    encodeU32 x.coverRateLiquidation ++ (← encodeNumber x.debtTotal) ++ (← encodeNumber x.debtMaximum) ++
    (← encodeNumber x.coverAvailable) ++ encodeU32 x.loanCount
def readLoanBroker (c : Cursor) : Except DecodeError (LoanBroker × Cursor) := do
  let (identity, c) ← readBrokerIdentity c; let (managementFeeRate, c) ← readU16 c
  let (coverRateMinimum, c) ← readU32 c; let (coverRateLiquidation, c) ← readU32 c
  let (debtTotal, c) ← readNumber c; let (debtMaximum, c) ← readNumber c
  let (coverAvailable, c) ← readNumber c; let (loanCount, c) ← readU32 c
  pure ({ identity, managementFeeRate, coverRateMinimum, coverRateLiquidation, debtTotal, debtMaximum, coverAvailable, loanCount }, c)

def encodeCoverResult (x : LoanBrokerCoverResult) : Except DecodeError ByteArray :=
  return encodeTER x.status ++ (← encodeSTAmount x.amount') ++ (← encodeLoanBroker x.loanBroker')
def readCoverResult (c : Cursor) : Except DecodeError (LoanBrokerCoverResult × Cursor) := do
  let (status, c) ← readTER c; let (amount', c) ← readSTAmount c; let (loanBroker', c) ← readLoanBroker c
  pure ({ status, amount', loanBroker' }, c)

end XRPL.FFI.Lending.Wire
