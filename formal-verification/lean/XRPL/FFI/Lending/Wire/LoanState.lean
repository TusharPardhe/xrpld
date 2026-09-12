import XRPL.FFI.Lending.Wire.VaultBroker
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Model.Lending.Loan.LoanResult

namespace XRPL.FFI.Lending.Wire

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault

def encodeLoanRates (x : LoanRates) : ByteArray :=
  encodeU32 x.interestRate ++ encodeU32 x.lateInterestRate ++ encodeU32 x.closeInterestRate ++
    encodeU32 x.overpaymentInterestRate ++ encodeU32 x.overpaymentFee
def readLoanRates (c : Cursor) : Except DecodeError (LoanRates × Cursor) := do
  let (interestRate, c) ← readU32 c; let (lateInterestRate, c) ← readU32 c
  let (closeInterestRate, c) ← readU32 c; let (overpaymentInterestRate, c) ← readU32 c; let (overpaymentFee, c) ← readU32 c
  pure ({ interestRate, lateInterestRate, closeInterestRate, overpaymentInterestRate, overpaymentFee }, c)

def encodeLoanFees (x : LoanFees) : Except DecodeError ByteArray :=
  return (← encodeNumber x.originationFee) ++ (← encodeNumber x.serviceFee) ++
    (← encodeNumber x.latePaymentFee) ++ (← encodeNumber x.closePaymentFee)
def readLoanFees (c : Cursor) : Except DecodeError (LoanFees × Cursor) := do
  let (originationFee, c) ← readNumber c; let (serviceFee, c) ← readNumber c
  let (latePaymentFee, c) ← readNumber c; let (closePaymentFee, c) ← readNumber c
  pure ({ originationFee, serviceFee, latePaymentFee, closePaymentFee }, c)

def encodeLoanSchedule (x : LoanSchedule) : ByteArray :=
  encodeU32 x.paymentInterval ++ encodeU32 x.paymentTotal ++ encodeU32 x.gracePeriod ++ encodeU32 x.startDate
def readLoanSchedule (c : Cursor) : Except DecodeError (LoanSchedule × Cursor) := do
  let (paymentInterval, c) ← readU32 c; let (paymentTotal, c) ← readU32 c
  let (gracePeriod, c) ← readU32 c; let (startDate, c) ← readU32 c
  pure ({ paymentInterval, paymentTotal, gracePeriod, startDate }, c)

def encodeLoan (x : Loan) : Except DecodeError ByteArray :=
  return (← encodeLoanIdentity x.identity) ++ (← encodeVaultIdentity x.vaultIdentity) ++ encodeLoanRates x.rates ++
    (← encodeLoanFees x.fees) ++ encodeLoanSchedule x.schedule ++ encodeU32 x.paymentRemaining ++
    (← encodeNumber x.periodicPayment) ++ (← encodeNumber x.principalOutstanding) ++
    (← encodeNumber x.totalValueOutstanding) ++ (← encodeNumber x.managementFeeOutstanding) ++ (← encodeInt x.loanScale) ++
    encodeU32 x.previousPaymentDueDate ++ encodeU32 x.nextPaymentDueDate ++ encodeBool x.isPending ++
    encodeBool x.isImpaired ++ encodeBool x.isDefault ++ encodeBool x.allowsOverpayment
def readLoan (c : Cursor) : Except DecodeError (Loan × Cursor) := do
  let (identity, c) ← readLoanIdentity c; let (vaultIdentity, c) ← readVaultIdentity c
  let (rates, c) ← readLoanRates c; let (fees, c) ← readLoanFees c; let (schedule, c) ← readLoanSchedule c
  let (paymentRemaining, c) ← readU32 c; let (periodicPayment, c) ← readNumber c; let (principalOutstanding, c) ← readNumber c
  let (totalValueOutstanding, c) ← readNumber c; let (managementFeeOutstanding, c) ← readNumber c; let (loanScale, c) ← readInt c
  let (previousPaymentDueDate, c) ← readU32 c; let (nextPaymentDueDate, c) ← readU32 c
  let (isPending, c) ← readBool c; let (isImpaired, c) ← readBool c; let (isDefault, c) ← readBool c; let (allowsOverpayment, c) ← readBool c
  pure (Loan.mk identity vaultIdentity rates fees schedule paymentRemaining periodicPayment principalOutstanding
    totalValueOutstanding managementFeeOutstanding loanScale previousPaymentDueDate nextPaymentDueDate
    isPending isImpaired isDefault allowsOverpayment, c)

def encodeLoanState (x : LoanState) : Except DecodeError ByteArray :=
  return (← encodeNumber x.valueOutstanding) ++ (← encodeNumber x.principalOutstanding) ++
    (← encodeNumber x.interestDue) ++ (← encodeNumber x.managementFeeDue)
def readLoanState (c : Cursor) : Except DecodeError (LoanState × Cursor) := do
  let (valueOutstanding, c) ← readNumber c; let (principalOutstanding, c) ← readNumber c
  let (interestDue, c) ← readNumber c; let (managementFeeDue, c) ← readNumber c
  pure ({ valueOutstanding, principalOutstanding, interestDue, managementFeeDue }, c)

def encodeLoanStateDeltas (x : LoanStateDeltas) : Except DecodeError ByteArray :=
  return (← encodeNumber x.totalValue) ++ (← encodeNumber x.principal) ++ (← encodeNumber x.interest) ++
    (← encodeNumber x.untrackedInterest) ++ (← encodeNumber x.managementFee) ++
    (← encodeNumber x.untrackedManagementFee) ++ encodeBool x.isFinal
def readLoanStateDeltas (c : Cursor) : Except DecodeError (LoanStateDeltas × Cursor) := do
  let (totalValue, c) ← readNumber c; let (principal, c) ← readNumber c; let (interest, c) ← readNumber c
  let (untrackedInterest, c) ← readNumber c; let (managementFee, c) ← readNumber c
  let (untrackedManagementFee, c) ← readNumber c; let (isFinal, c) ← readBool c
  pure ({ totalValue, principal, interest, untrackedInterest, managementFee, untrackedManagementFee, isFinal }, c)

def encodeBrokerVault (x : BrokerVault) : Except DecodeError ByteArray :=
  return (← encodeVaultIdentity x.vaultIdentity) ++ (← encodeVault x.vault) ++ (← encodeLoanBroker x.broker)
def readBrokerVault (c : Cursor) : Except DecodeError (BrokerVault × Cursor) := do
  let (vaultIdentity, c) ← readVaultIdentity c; let (vault, c) ← readVault c; let (broker, c) ← readLoanBroker c
  pure ({ vaultIdentity, vault, broker }, c)

def encodeLoanVault (x : LoanVault) : Except DecodeError ByteArray :=
  return (← encodeVaultIdentity x.vaultIdentity) ++ (← encodeLoan x.loan) ++ (← encodeVault x.vault)
def readLoanVault (c : Cursor) : Except DecodeError (LoanVault × Cursor) := do
  let (vaultIdentity, c) ← readVaultIdentity c; let (loan, c) ← readLoan c; let (vault, c) ← readVault c
  pure ({ vaultIdentity, loan, vault }, c)

def encodeLendingState (x : LendingState) : Except DecodeError ByteArray :=
  return (← encodeVaultIdentity x.vaultIdentity) ++ (← encodeVault x.vault) ++ (← encodeLoanBroker x.broker) ++ (← encodeLoan x.loan)
def readLendingState (c : Cursor) : Except DecodeError (LendingState × Cursor) := do
  let (vaultIdentity, c) ← readVaultIdentity c; let (vault, c) ← readVault c
  let (broker, c) ← readLoanBroker c; let (loan, c) ← readLoan c
  pure ({ vaultIdentity, vault, broker, loan }, c)

def encodeLoanResult (encode : α → Except DecodeError ByteArray) : LoanResult α → Except DecodeError ByteArray
  | .ok value => return one 0 ++ (← encode value)
  | .rejected value => .ok (one 1 ++ encodeTER value)
def readLoanResult (decode : Cursor → Except DecodeError (α × Cursor))
    (c : Cursor) : Except DecodeError (LoanResult α × Cursor) := do
  let offset := c.offset; let (tag, c) ← readU8 c
  match tag with
  | 0 => let (value, c) ← decode c; pure (.ok value, c)
  | 1 => let (value, c) ← readTER c; pure (.rejected value, c)
  | _ => .error (.badTag 0 tag)

def encodeLifecycleResult (encode : α → Except DecodeError ByteArray) : Except Error (LoanResult α) → Except DecodeError ByteArray
  | .ok value => return one 0 ++ (← encodeLoanResult encode value)
  | .error value => .ok (one 1 ++ encodeError value)
def readLifecycleResult (decode : Cursor → Except DecodeError (α × Cursor))
    (c : Cursor) : Except DecodeError (Except Error (LoanResult α) × Cursor) := do
  let (tag, c) ← readU8 c
  match tag with
  | 0 => let (value, c) ← readLoanResult decode c; pure (.ok value, c)
  | 1 => let (value, c) ← readError c; pure (.error value, c)
  | _ => .error (.badTag 0 tag)

end XRPL.FFI.Lending.Wire
