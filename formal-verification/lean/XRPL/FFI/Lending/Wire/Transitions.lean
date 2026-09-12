import XRPL.FFI.Lending.Wire.LoanState
import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanDelete
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Vault.Terminal

namespace XRPL.FFI.Lending.Wire

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault

/-- Frame either a successful result or the exact decoder failure.  In
particular, decode errors are not collapsed to a generic byte: callers can
reliably distinguish malformed magic, version, tags, truncation and canonicality
failures without dispatching a model transition. -/
def finish (tag : UInt8) (payload : Except DecodeError ByteArray) : ByteArray :=
  match encodeEnvelope tag (match payload with | .ok bytes => one 0 ++ bytes | .error error => one 1 ++ encodeDecodeError error) with
  | .ok bytes => bytes | .error _ => ByteArray.empty
def run (requestTag responseTag : UInt8) (decode : Cursor → Except DecodeError (α × Cursor))
    (encode : β → Except DecodeError ByteArray) (apply : α → β) (input : ByteArray) : ByteArray :=
  match decodeWhole requestTag decode input with
  | .error error => finish responseTag (.error error)
  | .ok request => finish responseTag (encode (apply request))

structure CreateRequest where
  vaultIdentity : VaultIdentity
  loanIdentity : LoanIdentity
  vault : Vault
  broker : LoanBroker
  principal : Number
  rates : LoanRates
  fees : LoanFees
  schedule : LoanSchedule
  allowsOverpayment : Bool
  pending : Bool

def readCreateRequest (c : Cursor) : Except DecodeError (CreateRequest × Cursor) := do
  let (vaultIdentity, c) ← readVaultIdentity c; let (loanIdentity, c) ← readLoanIdentity c
  let (vault, c) ← readVault c; let (broker, c) ← readLoanBroker c; let (principal, c) ← readNumber c
  let (rates, c) ← readLoanRates c; let (fees, c) ← readLoanFees c; let (schedule, c) ← readLoanSchedule c
  let (allowsOverpayment, c) ← readBool c; let (pending, c) ← readBool c
  pure ({ vaultIdentity, loanIdentity, vault, broker, principal, rates, fees, schedule, allowsOverpayment, pending }, c)

structure LoanVaultRequest where
  loan : Loan
  vault : Vault
def readLoanVaultRequest (c : Cursor) : Except DecodeError (LoanVaultRequest × Cursor) := do
  let (loan, c) ← readLoan c
  let (vault, c) ← readVault c
  pure ({ loan := loan, vault := vault }, c)
structure BrokerRequest where
  loan : Loan
  vault : Vault
  broker : LoanBroker
def readBrokerRequest (c : Cursor) : Except DecodeError (BrokerRequest × Cursor) := do
  let (loan, c) ← readLoan c
  let (vault, c) ← readVault c
  let (broker, c) ← readLoanBroker c
  pure ({ loan := loan, vault := vault, broker := broker }, c)

def readPaymentType (c : Cursor) : Except DecodeError (LoanPaymentType × Cursor) := do
  let (tag, c) ← readU8 c
  match tag with
  | 0 => pure (.regular, c)
  | 1 => pure (.late, c)
  | 2 => pure (.full, c)
  | 3 => pure (.overpayment, c)
  | _ => .error (.badTag 0 tag)
structure PaymentRequest where
  loan : Loan
  vault : Vault
  broker : LoanBroker
  paymentType : LoanPaymentType
  amount : Number
  now : UInt32
def readPaymentRequest (c : Cursor) : Except DecodeError (PaymentRequest × Cursor) := do
  let (base, c) ← readBrokerRequest c
  let (paymentType, c) ← readPaymentType c
  let (amount, c) ← readNumber c
  let (now, c) ← readU32 c
  pure ({ loan := base.loan, vault := base.vault, broker := base.broker, paymentType := paymentType, amount := amount, now := now }, c)
structure AmountRequest where
  loan : Loan
  vault : Vault
  broker : LoanBroker
  amount : Number
  now : UInt32
def readAmountRequest (c : Cursor) : Except DecodeError (AmountRequest × Cursor) := do
  let (base, c) ← readBrokerRequest c
  let (amount, c) ← readNumber c
  let (now, c) ← readU32 c
  pure ({ loan := base.loan, vault := base.vault, broker := base.broker, amount := amount, now := now }, c)
structure DefaultRequest where
  loan : Loan
  vault : Vault
  broker : LoanBroker
  impaired : Bool
def readDefaultRequest (c : Cursor) : Except DecodeError (DefaultRequest × Cursor) := do
  let (base, c) ← readBrokerRequest c
  let (impaired, c) ← readBool c
  pure ({ loan := base.loan, vault := base.vault, broker := base.broker, impaired := impaired }, c)

structure BrokerCreateRequest where
  identity : BrokerIdentity
  debtMaximum : Option Number
  managementFeeRate : Option UInt16
  coverRateMinimum : Option UInt32
  coverRateLiquidation : Option UInt32
def readBrokerCreateRequest (c : Cursor) : Except DecodeError (BrokerCreateRequest × Cursor) := do
  let (identity, c) ← readBrokerIdentity c
  let (debtMaximum, c) ← readOption readNumber c
  let (managementFeeRate, c) ← readOption readU16 c
  let (coverRateMinimum, c) ← readOption readU32 c
  let (coverRateLiquidation, c) ← readOption readU32 c
  pure (BrokerCreateRequest.mk identity debtMaximum managementFeeRate coverRateMinimum coverRateLiquidation, c)
structure BrokerUpdateRequest where
  broker : LoanBroker
  debtMaximum : Option Number
def readBrokerUpdateRequest (c : Cursor) : Except DecodeError (BrokerUpdateRequest × Cursor) := do
  let (broker, c) ← readLoanBroker c
  let (debtMaximum, c) ← readOption readNumber c
  pure ({ broker := broker, debtMaximum := debtMaximum }, c)
structure CoverRequest where
  broker : LoanBroker
  numericType : NumericType
  amount : STAmount
def readCoverRequest (c : Cursor) : Except DecodeError (CoverRequest × Cursor) := do
  let (broker, c) ← readLoanBroker c
  let (numericType, c) ← readNumericType c
  let (amount, c) ← readSTAmount c
  pure ({ broker := broker, numericType := numericType, amount := amount }, c)
structure CoverValidateRequest where
  numericType : NumericType
  coverAvailable : Number
  amount : STAmount
def readCoverValidateRequest (c : Cursor) : Except DecodeError (CoverValidateRequest × Cursor) := do
  let (numericType, c) ← readNumericType c
  let (coverAvailable, c) ← readNumber c
  let (amount, c) ← readSTAmount c
  pure ({ numericType := numericType, coverAvailable := coverAvailable, amount := amount }, c)

/-! ## Canonical request encoding

Each encoder below is the field-for-field inverse of its corresponding reader.
`encodeRequest` owns the single version-one envelope construction, so every
public route uses the same magic, version, tag, bounded payload length, and no
trailing bytes.  The route-specific aliases deliberately retain distinct names:
raw and terminal transitions have distinct request tags even where they share
an operation payload. -/
def encodeCreateRequest (x : CreateRequest) : Except DecodeError ByteArray :=
  return (← encodeVaultIdentity x.vaultIdentity) ++ (← encodeLoanIdentity x.loanIdentity) ++
    (← encodeVault x.vault) ++ (← encodeLoanBroker x.broker) ++ (← encodeNumber x.principal) ++
    encodeLoanRates x.rates ++ (← encodeLoanFees x.fees) ++ encodeLoanSchedule x.schedule ++
    encodeBool x.allowsOverpayment ++ encodeBool x.pending

def encodeLoanVaultRequest (x : LoanVaultRequest) : Except DecodeError ByteArray :=
  return (← encodeLoan x.loan) ++ (← encodeVault x.vault)

def encodeBrokerRequest (x : BrokerRequest) : Except DecodeError ByteArray :=
  return (← encodeLoan x.loan) ++ (← encodeVault x.vault) ++ (← encodeLoanBroker x.broker)

def encodePaymentType : LoanPaymentType → ByteArray
  | .regular => one 0
  | .late => one 1
  | .full => one 2
  | .overpayment => one 3

def encodePaymentRequest (x : PaymentRequest) : Except DecodeError ByteArray :=
  return (← encodeBrokerRequest { loan := x.loan, vault := x.vault, broker := x.broker }) ++
    encodePaymentType x.paymentType ++ (← encodeNumber x.amount) ++ encodeU32 x.now

def encodeAmountRequest (x : AmountRequest) : Except DecodeError ByteArray :=
  return (← encodeBrokerRequest { loan := x.loan, vault := x.vault, broker := x.broker }) ++
    (← encodeNumber x.amount) ++ encodeU32 x.now

def encodeDefaultRequest (x : DefaultRequest) : Except DecodeError ByteArray :=
  return (← encodeBrokerRequest { loan := x.loan, vault := x.vault, broker := x.broker }) ++
    encodeBool x.impaired

def encodeBrokerCreateRequest (x : BrokerCreateRequest) : Except DecodeError ByteArray :=
  return (← encodeBrokerIdentity x.identity) ++ (← encodeOption encodeNumber x.debtMaximum) ++
    (← encodeOption (fun value => .ok (encodeU16 value)) x.managementFeeRate) ++
    (← encodeOption (fun value => .ok (encodeU32 value)) x.coverRateMinimum) ++
    (← encodeOption (fun value => .ok (encodeU32 value)) x.coverRateLiquidation)

def encodeBrokerUpdateRequest (x : BrokerUpdateRequest) : Except DecodeError ByteArray :=
  return (← encodeLoanBroker x.broker) ++ (← encodeOption encodeNumber x.debtMaximum)

def encodeCoverRequest (x : CoverRequest) : Except DecodeError ByteArray :=
  return (← encodeLoanBroker x.broker) ++ (← encodeNumericType x.numericType) ++ (← encodeSTAmount x.amount)

def encodeCoverValidateRequest (x : CoverValidateRequest) : Except DecodeError ByteArray :=
  return (← encodeNumericType x.numericType) ++ (← encodeNumber x.coverAvailable) ++ (← encodeSTAmount x.amount)

/-- Version-frame a canonical request payload.  All public aliases below route
through this helper rather than duplicating envelope logic. -/
def encodeRequest (tag : UInt8) (encode : α → Except DecodeError ByteArray) (value : α) :
    Except DecodeError ByteArray := do
  encodeEnvelope tag (← encode value)

def encodeRawCreateRequest := encodeRequest 1 encodeCreateRequest
def encodeRawCreatePendingRequest := encodeRequest 2 encodeCreateRequest
def encodeRawCreateImmediateRequest := encodeRequest 3 encodeCreateRequest
def encodeTerminalCreateRequest := encodeRequest 17 encodeCreateRequest
def encodeTerminalCreatePendingRequest := encodeRequest 18 encodeCreateRequest
def encodeTerminalCreateImmediateRequest := encodeRequest 19 encodeCreateRequest
def encodeRawAcceptRequest := encodeRequest 4 encodeLoanVaultRequest
def encodeTerminalAcceptRequest := encodeRequest 20 encodeLoanVaultRequest
def encodeRawDeleteRequest := encodeRequest 5 encodeBrokerRequest
def encodeTerminalDeleteRequest := encodeRequest 21 encodeBrokerRequest
def encodeRawRegularRequest := encodeRequest 6 encodePaymentRequest
def encodeTerminalRegularRequest := encodeRequest 22 encodePaymentRequest
def encodeRawLateRequest := encodeRequest 7 encodeAmountRequest
def encodeTerminalLateRequest := encodeRequest 23 encodeAmountRequest
def encodeRawFullRequest := encodeRequest 8 encodeAmountRequest
def encodeTerminalFullRequest := encodeRequest 24 encodeAmountRequest
def encodeRawImpairRequest := encodeRequest 9 encodeLoanVaultRequest
def encodeTerminalImpairRequest := encodeRequest 25 encodeLoanVaultRequest
def encodeRawUnimpairedRequest := encodeRequest 10 encodeLoanVaultRequest
def encodeTerminalUnimpairedRequest := encodeRequest 26 encodeLoanVaultRequest
def encodeRawDefaultRequest := encodeRequest 11 encodeDefaultRequest
def encodeTerminalDefaultRequest := encodeRequest 27 encodeDefaultRequest
def encodeRawBrokerCreateRequest := encodeRequest 12 encodeBrokerCreateRequest
def encodeRawBrokerUpdateRequest := encodeRequest 13 encodeBrokerUpdateRequest
def encodeRawCoverValidateRequest := encodeRequest 14 encodeCoverValidateRequest
def encodeRawCoverDepositRequest := encodeRequest 15 encodeCoverRequest
def encodeRawCoverWithdrawRequest := encodeRequest 16 encodeCoverRequest

def encodeBrokerOnly (x : LoanBroker) : Except DecodeError ByteArray := encodeLoanBroker x
def encodeVaultResult (x : Except Error (LoanResult Vault)) : Except DecodeError ByteArray := encodeLifecycleResult encodeVault x
def encodeStateResult (x : Except Error (LoanResult LendingState)) : Except DecodeError ByteArray := encodeLifecycleResult encodeLendingState x
def encodeBrokerResult (x : Except Error (LoanResult BrokerVault)) : Except DecodeError ByteArray := encodeLifecycleResult encodeBrokerVault x
def encodeLoanVaultResult (x : Except Error (LoanResult LoanVault)) : Except DecodeError ByteArray := encodeLifecycleResult encodeLoanVault x
def encodeCover (x : Except Error LoanBrokerCoverResult) : Except DecodeError ByteArray :=
  match x with | .ok value => return one 0 ++ (← encodeCoverResult value) | .error error => .ok (one 1 ++ encodeError error)
def encodeTERResult (x : Except Error TER) : Except DecodeError ByteArray :=
  match x with | .ok value => .ok (one 0 ++ encodeTER value) | .error error => .ok (one 1 ++ encodeError error)

@[export lean_lending_raw_create_wire] def rawCreateWire := run 1 129 readCreateRequest encodeStateResult fun r => Loan.create r.vaultIdentity r.loanIdentity r.vault r.broker r.principal r.rates r.fees r.schedule r.allowsOverpayment r.pending
@[export lean_lending_raw_create_pending_wire] def rawCreatePendingWire := run 2 130 readCreateRequest encodeStateResult fun r => Loan.createPending r.vaultIdentity r.loanIdentity r.vault r.broker r.principal r.rates r.fees r.schedule r.allowsOverpayment
@[export lean_lending_raw_create_immediate_wire] def rawCreateImmediateWire := run 3 131 readCreateRequest encodeStateResult fun r => Loan.createImmediate r.vaultIdentity r.loanIdentity r.vault r.broker r.principal r.rates r.fees r.schedule r.allowsOverpayment
@[export lean_lending_terminal_create_wire] def terminalCreateWire := run 17 145 readCreateRequest encodeStateResult fun r => Loan.create_terminal r.vaultIdentity r.loanIdentity r.vault r.broker r.principal r.rates r.fees r.schedule r.allowsOverpayment r.pending
@[export lean_lending_terminal_create_pending_wire] def terminalCreatePendingWire := run 18 146 readCreateRequest encodeStateResult fun r => Loan.createPending_terminal r.vaultIdentity r.loanIdentity r.vault r.broker r.principal r.rates r.fees r.schedule r.allowsOverpayment
@[export lean_lending_terminal_create_immediate_wire] def terminalCreateImmediateWire := run 19 147 readCreateRequest encodeStateResult fun r => Loan.createImmediate_terminal r.vaultIdentity r.loanIdentity r.vault r.broker r.principal r.rates r.fees r.schedule r.allowsOverpayment
@[export lean_lending_raw_accept_wire] def rawAcceptWire := run 4 132 readLoanVaultRequest encodeLoanVaultResult fun r => Loan.accept r.loan r.vault
@[export lean_lending_terminal_accept_wire] def terminalAcceptWire := run 20 148 readLoanVaultRequest encodeLoanVaultResult fun r => Loan.accept_terminal r.loan r.vault
@[export lean_lending_raw_delete_wire] def rawDeleteWire := run 5 133 readBrokerRequest encodeBrokerResult fun r => Loan.delete r.loan r.vault r.broker
@[export lean_lending_terminal_delete_wire] def terminalDeleteWire := run 21 149 readBrokerRequest encodeBrokerResult fun r => Loan.delete_terminal r.loan r.vault r.broker
@[export lean_lending_raw_regular_payment_wire] def rawRegularWire := run 6 134 readPaymentRequest encodeStateResult fun r => Loan.regularPayment r.loan r.vault r.broker r.paymentType r.amount r.now
@[export lean_lending_terminal_regular_payment_wire] def terminalRegularWire := run 22 150 readPaymentRequest encodeStateResult fun r => Loan.regularPayment_terminal r.loan r.vault r.broker r.paymentType r.amount r.now
@[export lean_lending_raw_late_payment_wire] def rawLateWire := run 7 135 readAmountRequest encodeStateResult fun r => Loan.latePayment r.loan r.vault r.broker r.amount r.now
@[export lean_lending_terminal_late_payment_wire] def terminalLateWire := run 23 151 readAmountRequest encodeStateResult fun r => Loan.latePayment_terminal r.loan r.vault r.broker r.amount r.now
@[export lean_lending_raw_full_payment_wire] def rawFullWire := run 8 136 readAmountRequest encodeStateResult fun r => Loan.fullPayment r.loan r.vault r.broker r.amount r.now
@[export lean_lending_terminal_full_payment_wire] def terminalFullWire := run 24 152 readAmountRequest encodeStateResult fun r => Loan.fullPayment_terminal r.loan r.vault r.broker r.amount r.now
@[export lean_lending_raw_manage_impair_wire] def rawImpairWire := run 9 137 readLoanVaultRequest encodeVaultResult fun r => Loan.manageImpair r.loan r.vault
@[export lean_lending_terminal_manage_impair_wire] def terminalImpairWire := run 25 153 readLoanVaultRequest encodeVaultResult fun r => Loan.manageImpair_terminal r.loan r.vault
@[export lean_lending_raw_manage_unimpair_wire] def rawUnimpairedWire := run 10 138 readLoanVaultRequest encodeVaultResult fun r => Loan.manageUnimpair r.loan r.vault
@[export lean_lending_terminal_manage_unimpair_wire] def terminalUnimpairedWire := run 26 154 readLoanVaultRequest encodeVaultResult fun r => Loan.manageUnimpair_terminal r.loan r.vault
@[export lean_lending_raw_manage_default_wire] def rawDefaultWire := run 11 139 readDefaultRequest encodeBrokerResult fun r => Loan.manageDefault r.loan r.vault r.broker r.impaired
@[export lean_lending_terminal_manage_default_wire] def terminalDefaultWire := run 27 155 readDefaultRequest encodeBrokerResult fun r => Loan.manageDefault_terminal r.loan r.vault r.broker r.impaired
@[export lean_lending_raw_broker_create_wire] def rawBrokerCreateWire := run 12 140 readBrokerCreateRequest encodeBrokerOnly fun r => LoanBroker.create r.identity ({ debtMaximum := r.debtMaximum, managementFeeRate := r.managementFeeRate, coverRateMinimum := r.coverRateMinimum, coverRateLiquidation := r.coverRateLiquidation })
@[export lean_lending_raw_broker_update_wire] def rawBrokerUpdateWire := run 13 141 readBrokerUpdateRequest encodeBrokerOnly fun r => LoanBroker.update r.broker r.debtMaximum
@[export lean_lending_raw_cover_validate_wire] def rawCoverValidateWire := run 14 142 readCoverValidateRequest encodeTERResult fun r => canApplyToBrokerCover r.numericType r.coverAvailable r.amount
@[export lean_lending_raw_cover_deposit_wire] def rawCoverDepositWire := run 15 143 readCoverRequest encodeCover fun r => LoanBroker.coverDeposit r.broker r.numericType r.amount
@[export lean_lending_raw_cover_withdraw_wire] def rawCoverWithdrawWire := run 16 144 readCoverRequest encodeCover fun r => LoanBroker.coverWithdraw r.broker r.numericType r.amount

end XRPL.FFI.Lending.Wire
