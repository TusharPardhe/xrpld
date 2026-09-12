import XRPL.FFI.Lending.Wire.Transitions

/-! Malformed-envelope atomicity for every public Lending wire wrapper. -/
namespace XRPL.Properties.Lending.Wire

open XRPL.FFI.Lending.Wire
open XRPL.Model.Lending

private theorem run_bad_magic_atomic
    (requestTag responseTag : UInt8)
    (decode : Cursor → Except DecodeError (α × Cursor))
    (encode : β → Except DecodeError ByteArray)
    (apply : α → β) :
    run requestTag responseTag decode encode apply (encodeU32 0) =
      finish responseTag (.error .badMagic) := by
  rfl

/-- The fixed malformed input fails framing before any model operation can run. -/
theorem raw_create_bad_magic_atomic : rawCreateWire (encodeU32 0) = finish 129 (.error .badMagic) := by rfl
theorem raw_create_pending_bad_magic_atomic : rawCreatePendingWire (encodeU32 0) = finish 130 (.error .badMagic) := by rfl
theorem raw_create_immediate_bad_magic_atomic : rawCreateImmediateWire (encodeU32 0) = finish 131 (.error .badMagic) := by rfl
theorem terminal_create_bad_magic_atomic : terminalCreateWire (encodeU32 0) = finish 145 (.error .badMagic) := by rfl
theorem terminal_create_pending_bad_magic_atomic : terminalCreatePendingWire (encodeU32 0) = finish 146 (.error .badMagic) := by rfl
theorem terminal_create_immediate_bad_magic_atomic : terminalCreateImmediateWire (encodeU32 0) = finish 147 (.error .badMagic) := by rfl
theorem raw_accept_bad_magic_atomic : rawAcceptWire (encodeU32 0) = finish 132 (.error .badMagic) := by rfl
theorem terminal_accept_bad_magic_atomic : terminalAcceptWire (encodeU32 0) = finish 148 (.error .badMagic) := by rfl
theorem raw_delete_bad_magic_atomic : rawDeleteWire (encodeU32 0) = finish 133 (.error .badMagic) := by rfl
theorem terminal_delete_bad_magic_atomic : terminalDeleteWire (encodeU32 0) = finish 149 (.error .badMagic) := by rfl
theorem raw_regular_bad_magic_atomic : rawRegularWire (encodeU32 0) = finish 134 (.error .badMagic) := by rfl
theorem terminal_regular_bad_magic_atomic : terminalRegularWire (encodeU32 0) = finish 150 (.error .badMagic) := by rfl
theorem raw_late_bad_magic_atomic : rawLateWire (encodeU32 0) = finish 135 (.error .badMagic) := by rfl
theorem terminal_late_bad_magic_atomic : terminalLateWire (encodeU32 0) = finish 151 (.error .badMagic) := by rfl
theorem raw_full_bad_magic_atomic : rawFullWire (encodeU32 0) = finish 136 (.error .badMagic) := by rfl
theorem terminal_full_bad_magic_atomic : terminalFullWire (encodeU32 0) = finish 152 (.error .badMagic) := by rfl
theorem raw_impair_bad_magic_atomic : rawImpairWire (encodeU32 0) = finish 137 (.error .badMagic) := by rfl
theorem terminal_impair_bad_magic_atomic : terminalImpairWire (encodeU32 0) = finish 153 (.error .badMagic) := by rfl
theorem raw_unimpair_bad_magic_atomic : rawUnimpairedWire (encodeU32 0) = finish 138 (.error .badMagic) := by rfl
theorem terminal_unimpair_bad_magic_atomic : terminalUnimpairedWire (encodeU32 0) = finish 154 (.error .badMagic) := by rfl
theorem raw_default_bad_magic_atomic : rawDefaultWire (encodeU32 0) = finish 139 (.error .badMagic) := by rfl
theorem terminal_default_bad_magic_atomic : terminalDefaultWire (encodeU32 0) = finish 155 (.error .badMagic) := by rfl
theorem raw_broker_create_bad_magic_atomic : rawBrokerCreateWire (encodeU32 0) = finish 140 (.error .badMagic) := by rfl
theorem raw_broker_update_bad_magic_atomic : rawBrokerUpdateWire (encodeU32 0) = finish 141 (.error .badMagic) := by rfl
theorem raw_cover_validate_bad_magic_atomic : rawCoverValidateWire (encodeU32 0) = finish 142 (.error .badMagic) := by rfl
theorem raw_cover_deposit_bad_magic_atomic : rawCoverDepositWire (encodeU32 0) = finish 143 (.error .badMagic) := by rfl
theorem raw_cover_withdraw_bad_magic_atomic : rawCoverWithdrawWire (encodeU32 0) = finish 144 (.error .badMagic) := by rfl

/-- The response distinguishes bad magic from a generic failure. -/
theorem encoded_bad_magic_is_specific : encodeDecodeError .badMagic = one 2 := rfl

/-- Every malformed input is rejected before `apply` can be evaluated; this is
quantified over the decoder error rather than limited to one malformed vector. -/
theorem run_decode_failure_atomic
    (requestTag responseTag : UInt8)
    (decode : Cursor → Except DecodeError (α × Cursor))
    (encode : β → Except DecodeError ByteArray)
    (apply : α → β)
    (input : ByteArray) (error : DecodeError)
    (h : decodeWhole requestTag decode input = .error error) :
    run requestTag responseTag decode encode apply input = finish responseTag (.error error) := by
  simp [run, h]

/-- On a successful decode, exactly the supplied model operation is evaluated
and its complete encoded value or error is returned in the response envelope. -/
theorem run_decode_success_exact
    (requestTag responseTag : UInt8)
    (decode : Cursor → Except DecodeError (α × Cursor))
    (encode : β → Except DecodeError ByteArray)
    (apply : α → β)
    (input : ByteArray) (request : α)
    (h : decodeWhole requestTag decode input = .ok request) :
    run requestTag responseTag decode encode apply input = finish responseTag (encode (apply request)) := by
  simp [run, h]

private theorem route_failure
    {α β : Type} {requestTag responseTag : UInt8}
    {decode : Cursor → Except DecodeError (α × Cursor)}
    {encode : β → Except DecodeError ByteArray} {apply : α → β}
    (input : ByteArray) (error : DecodeError)
    (h : decodeWhole requestTag decode input = .error error) :
    run requestTag responseTag decode encode apply input = finish responseTag (.error error) :=
  run_decode_failure_atomic requestTag responseTag decode encode apply input error h

/-- Universal no-dispatch equations, one for every exported wire wrapper. -/
theorem raw_create_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 1 readCreateRequest input = .error error) : rawCreateWire input = finish 129 (.error error) :=
  route_failure input error h
theorem raw_create_pending_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 2 readCreateRequest input = .error error) : rawCreatePendingWire input = finish 130 (.error error) :=
  route_failure input error h
theorem raw_create_immediate_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 3 readCreateRequest input = .error error) : rawCreateImmediateWire input = finish 131 (.error error) :=
  route_failure input error h
theorem terminal_create_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 17 readCreateRequest input = .error error) : terminalCreateWire input = finish 145 (.error error) :=
  route_failure input error h
theorem terminal_create_pending_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 18 readCreateRequest input = .error error) : terminalCreatePendingWire input = finish 146 (.error error) :=
  route_failure input error h
theorem terminal_create_immediate_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 19 readCreateRequest input = .error error) : terminalCreateImmediateWire input = finish 147 (.error error) :=
  route_failure input error h
theorem raw_accept_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 4 readLoanVaultRequest input = .error error) : rawAcceptWire input = finish 132 (.error error) := route_failure input error h
theorem terminal_accept_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 20 readLoanVaultRequest input = .error error) : terminalAcceptWire input = finish 148 (.error error) := route_failure input error h
theorem raw_delete_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 5 readBrokerRequest input = .error error) : rawDeleteWire input = finish 133 (.error error) := route_failure input error h
theorem terminal_delete_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 21 readBrokerRequest input = .error error) : terminalDeleteWire input = finish 149 (.error error) := route_failure input error h
theorem raw_regular_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 6 readPaymentRequest input = .error error) : rawRegularWire input = finish 134 (.error error) := route_failure input error h
theorem terminal_regular_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 22 readPaymentRequest input = .error error) : terminalRegularWire input = finish 150 (.error error) := route_failure input error h
theorem raw_late_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 7 readAmountRequest input = .error error) : rawLateWire input = finish 135 (.error error) := route_failure input error h
theorem terminal_late_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 23 readAmountRequest input = .error error) : terminalLateWire input = finish 151 (.error error) := route_failure input error h
theorem raw_full_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 8 readAmountRequest input = .error error) : rawFullWire input = finish 136 (.error error) := route_failure input error h
theorem terminal_full_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 24 readAmountRequest input = .error error) : terminalFullWire input = finish 152 (.error error) := route_failure input error h
theorem raw_impair_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 9 readLoanVaultRequest input = .error error) : rawImpairWire input = finish 137 (.error error) := route_failure input error h
theorem terminal_impair_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 25 readLoanVaultRequest input = .error error) : terminalImpairWire input = finish 153 (.error error) := route_failure input error h
theorem raw_unimpaired_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 10 readLoanVaultRequest input = .error error) : rawUnimpairedWire input = finish 138 (.error error) := route_failure input error h
theorem terminal_unimpaired_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 26 readLoanVaultRequest input = .error error) : terminalUnimpairedWire input = finish 154 (.error error) := route_failure input error h
theorem raw_default_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 11 readDefaultRequest input = .error error) : rawDefaultWire input = finish 139 (.error error) := route_failure input error h
theorem terminal_default_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 27 readDefaultRequest input = .error error) : terminalDefaultWire input = finish 155 (.error error) := route_failure input error h
theorem raw_broker_create_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 12 readBrokerCreateRequest input = .error error) : rawBrokerCreateWire input = finish 140 (.error error) := route_failure input error h
theorem raw_broker_update_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 13 readBrokerUpdateRequest input = .error error) : rawBrokerUpdateWire input = finish 141 (.error error) := route_failure input error h
theorem raw_cover_validate_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 14 readCoverValidateRequest input = .error error) : rawCoverValidateWire input = finish 142 (.error error) := route_failure input error h
theorem raw_cover_deposit_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 15 readCoverRequest input = .error error) : rawCoverDepositWire input = finish 143 (.error error) := route_failure input error h
theorem raw_cover_withdraw_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 16 readCoverRequest input = .error error) : rawCoverWithdrawWire input = finish 144 (.error error) := route_failure input error h


/-- Route-specific success equations make each public wrapper's model dispatch
and complete result encoding explicit after the shared whole-message gate. -/
theorem raw_create_decode_success_exact (input : ByteArray) (request : CreateRequest)
    (h : decodeWhole 1 readCreateRequest input = .ok request) :
    rawCreateWire input = finish 129 (encodeStateResult
      (Loan.create request.vaultIdentity request.loanIdentity request.vault request.broker request.principal
        request.rates request.fees request.schedule request.allowsOverpayment request.pending)) := by
  simp [rawCreateWire, run, h]

theorem raw_create_pending_decode_success_exact (input : ByteArray) (request : CreateRequest)
    (h : decodeWhole 2 readCreateRequest input = .ok request) :
    rawCreatePendingWire input = finish 130 (encodeStateResult
      (Loan.createPending request.vaultIdentity request.loanIdentity request.vault request.broker request.principal
        request.rates request.fees request.schedule request.allowsOverpayment)) := by
  simp [rawCreatePendingWire, run, h]

theorem raw_create_immediate_decode_success_exact (input : ByteArray) (request : CreateRequest)
    (h : decodeWhole 3 readCreateRequest input = .ok request) :
    rawCreateImmediateWire input = finish 131 (encodeStateResult
      (Loan.createImmediate request.vaultIdentity request.loanIdentity request.vault request.broker request.principal
        request.rates request.fees request.schedule request.allowsOverpayment)) := by
  simp [rawCreateImmediateWire, run, h]


theorem terminal_create_decode_success_exact (input : ByteArray) (request : CreateRequest)
    (h : decodeWhole 17 readCreateRequest input = .ok request) :
    terminalCreateWire input = finish 145 (encodeStateResult
      (Loan.create_terminal request.vaultIdentity request.loanIdentity request.vault request.broker request.principal
        request.rates request.fees request.schedule request.allowsOverpayment request.pending)) := by
  simp [terminalCreateWire, run, h]

theorem terminal_create_pending_decode_success_exact (input : ByteArray) (request : CreateRequest)
    (h : decodeWhole 18 readCreateRequest input = .ok request) :
    terminalCreatePendingWire input = finish 146 (encodeStateResult
      (Loan.createPending_terminal request.vaultIdentity request.loanIdentity request.vault request.broker request.principal
        request.rates request.fees request.schedule request.allowsOverpayment)) := by
  simp [terminalCreatePendingWire, run, h]

theorem terminal_create_immediate_decode_success_exact (input : ByteArray) (request : CreateRequest)
    (h : decodeWhole 19 readCreateRequest input = .ok request) :
    terminalCreateImmediateWire input = finish 147 (encodeStateResult
      (Loan.createImmediate_terminal request.vaultIdentity request.loanIdentity request.vault request.broker request.principal
        request.rates request.fees request.schedule request.allowsOverpayment)) := by
  simp [terminalCreateImmediateWire, run, h]

theorem raw_accept_decode_success_exact (input : ByteArray) (request : LoanVaultRequest)
    (h : decodeWhole 4 readLoanVaultRequest input = .ok request) :
    rawAcceptWire input = finish 132 (encodeLoanVaultResult (Loan.accept request.loan request.vault)) := by
  simp [rawAcceptWire, run, h]

theorem terminal_accept_decode_success_exact (input : ByteArray) (request : LoanVaultRequest)
    (h : decodeWhole 20 readLoanVaultRequest input = .ok request) :
    terminalAcceptWire input = finish 148 (encodeLoanVaultResult (Loan.accept_terminal request.loan request.vault)) := by
  simp [terminalAcceptWire, run, h]

theorem raw_delete_decode_success_exact (input : ByteArray) (request : BrokerRequest)
    (h : decodeWhole 5 readBrokerRequest input = .ok request) :
    rawDeleteWire input = finish 133 (encodeBrokerResult (Loan.delete request.loan request.vault request.broker)) := by
  simp [rawDeleteWire, run, h]

theorem terminal_delete_decode_success_exact (input : ByteArray) (request : BrokerRequest)
    (h : decodeWhole 21 readBrokerRequest input = .ok request) :
    terminalDeleteWire input = finish 149 (encodeBrokerResult (Loan.delete_terminal request.loan request.vault request.broker)) := by
  simp [terminalDeleteWire, run, h]

theorem raw_regular_decode_success_exact (input : ByteArray) (request : PaymentRequest)
    (h : decodeWhole 6 readPaymentRequest input = .ok request) :
    rawRegularWire input = finish 134 (encodeStateResult
      (Loan.regularPayment request.loan request.vault request.broker request.paymentType request.amount request.now)) := by
  simp [rawRegularWire, run, h]

theorem terminal_regular_decode_success_exact (input : ByteArray) (request : PaymentRequest)
    (h : decodeWhole 22 readPaymentRequest input = .ok request) :
    terminalRegularWire input = finish 150 (encodeStateResult
      (Loan.regularPayment_terminal request.loan request.vault request.broker request.paymentType request.amount request.now)) := by
  simp [terminalRegularWire, run, h]

theorem raw_late_decode_success_exact (input : ByteArray) (request : AmountRequest)
    (h : decodeWhole 7 readAmountRequest input = .ok request) :
    rawLateWire input = finish 135 (encodeStateResult
      (Loan.latePayment request.loan request.vault request.broker request.amount request.now)) := by
  simp [rawLateWire, run, h]

theorem terminal_late_decode_success_exact (input : ByteArray) (request : AmountRequest)
    (h : decodeWhole 23 readAmountRequest input = .ok request) :
    terminalLateWire input = finish 151 (encodeStateResult
      (Loan.latePayment_terminal request.loan request.vault request.broker request.amount request.now)) := by
  simp [terminalLateWire, run, h]

theorem raw_full_decode_success_exact (input : ByteArray) (request : AmountRequest)
    (h : decodeWhole 8 readAmountRequest input = .ok request) :
    rawFullWire input = finish 136 (encodeStateResult
      (Loan.fullPayment request.loan request.vault request.broker request.amount request.now)) := by
  simp [rawFullWire, run, h]

theorem terminal_full_decode_success_exact (input : ByteArray) (request : AmountRequest)
    (h : decodeWhole 24 readAmountRequest input = .ok request) :
    terminalFullWire input = finish 152 (encodeStateResult
      (Loan.fullPayment_terminal request.loan request.vault request.broker request.amount request.now)) := by
  simp [terminalFullWire, run, h]

theorem raw_impair_decode_success_exact (input : ByteArray) (request : LoanVaultRequest)
    (h : decodeWhole 9 readLoanVaultRequest input = .ok request) :
    rawImpairWire input = finish 137 (encodeVaultResult (Loan.manageImpair request.loan request.vault)) := by
  simp [rawImpairWire, run, h]

theorem terminal_impair_decode_success_exact (input : ByteArray) (request : LoanVaultRequest)
    (h : decodeWhole 25 readLoanVaultRequest input = .ok request) :
    terminalImpairWire input = finish 153 (encodeVaultResult (Loan.manageImpair_terminal request.loan request.vault)) := by
  simp [terminalImpairWire, run, h]

theorem raw_unimpaired_decode_success_exact (input : ByteArray) (request : LoanVaultRequest)
    (h : decodeWhole 10 readLoanVaultRequest input = .ok request) :
    rawUnimpairedWire input = finish 138 (encodeVaultResult (Loan.manageUnimpair request.loan request.vault)) := by
  simp [rawUnimpairedWire, run, h]

theorem terminal_unimpaired_decode_success_exact (input : ByteArray) (request : LoanVaultRequest)
    (h : decodeWhole 26 readLoanVaultRequest input = .ok request) :
    terminalUnimpairedWire input = finish 154 (encodeVaultResult (Loan.manageUnimpair_terminal request.loan request.vault)) := by
  simp [terminalUnimpairedWire, run, h]

theorem raw_default_decode_success_exact (input : ByteArray) (request : DefaultRequest)
    (h : decodeWhole 11 readDefaultRequest input = .ok request) :
    rawDefaultWire input = finish 139 (encodeBrokerResult
      (Loan.manageDefault request.loan request.vault request.broker request.impaired)) := by
  simp [rawDefaultWire, run, h]

theorem terminal_default_decode_success_exact (input : ByteArray) (request : DefaultRequest)
    (h : decodeWhole 27 readDefaultRequest input = .ok request) :
    terminalDefaultWire input = finish 155 (encodeBrokerResult
      (Loan.manageDefault_terminal request.loan request.vault request.broker request.impaired)) := by
  simp [terminalDefaultWire, run, h]

theorem raw_broker_create_decode_success_exact (input : ByteArray) (request : BrokerCreateRequest)
    (h : decodeWhole 12 readBrokerCreateRequest input = .ok request) :
    rawBrokerCreateWire input = finish 140 (encodeBrokerOnly
      (LoanBroker.create request.identity (LoanBrokerSetCreate.mk request.debtMaximum request.managementFeeRate
        request.coverRateMinimum request.coverRateLiquidation))) := by
  simp [rawBrokerCreateWire, run, h]

theorem raw_broker_update_decode_success_exact (input : ByteArray) (request : BrokerUpdateRequest)
    (h : decodeWhole 13 readBrokerUpdateRequest input = .ok request) :
    rawBrokerUpdateWire input = finish 141 (encodeBrokerOnly (LoanBroker.update request.broker request.debtMaximum)) := by
  simp [rawBrokerUpdateWire, run, h]

theorem raw_cover_validate_decode_success_exact (input : ByteArray) (request : CoverValidateRequest)
    (h : decodeWhole 14 readCoverValidateRequest input = .ok request) :
    rawCoverValidateWire input = finish 142 (encodeTERResult
      (canApplyToBrokerCover request.numericType request.coverAvailable request.amount)) := by
  simp [rawCoverValidateWire, run, h]

theorem raw_cover_deposit_decode_success_exact (input : ByteArray) (request : CoverRequest)
    (h : decodeWhole 15 readCoverRequest input = .ok request) :
    rawCoverDepositWire input = finish 143 (encodeCover
      (LoanBroker.coverDeposit request.broker request.numericType request.amount)) := by
  simp [rawCoverDepositWire, run, h]

theorem raw_cover_withdraw_decode_success_exact (input : ByteArray) (request : CoverRequest)
    (h : decodeWhole 16 readCoverRequest input = .ok request) :
    rawCoverWithdrawWire input = finish 144 (encodeCover
      (LoanBroker.coverWithdraw request.broker request.numericType request.amount)) := by
  simp [rawCoverWithdrawWire, run, h]

end XRPL.Properties.Lending.Wire
