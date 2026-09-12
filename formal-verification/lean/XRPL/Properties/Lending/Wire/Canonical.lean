import XRPL.FFI.Lending.Wire.Transitions

/-! ## Canonical, whole-value Lending wire codecs

`WireEncodable` is deliberately stronger than merely saying that an encoder
returns bytes.  It records the exact bytes, exact decoded value, and the fact
that the decoder consumes the *entire* cursor.  This is the common canonical
or well-formed domain for all version-one Lending codecs: values outside the
domain (for example an unnormalised `Number`, a negative zero, or an out of
range `Int`) have no such witness.
-/
namespace XRPL.Properties.Lending.Wire

open XRPL.FFI.Lending.Wire
open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault

/-- Exact canonical wire encodability.  In addition to an encoder success,
this requires the paired decoder to return the original value and to leave no
unconsumed byte. -/
def WireEncodable {α : Type}
    (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (value : α) : Prop :=
  ∃ bytes, encode value = .ok bytes ∧
    decode (Cursor.initial bytes) = .ok (value, { bytes := bytes, offset := bytes.size })

/-- The cursor component of `WireEncodable` is the full-consumption contract. -/
def WireFullyConsumed {α : Type}
    (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (value : α) : Prop :=
  ∃ bytes, encode value = .ok bytes ∧
    decode (Cursor.initial bytes) = .ok (value, { bytes := bytes, offset := bytes.size }) ∧
    ({ bytes := bytes, offset := bytes.size } : Cursor).remaining = 0

private theorem terminal_cursor_remaining (bytes : ByteArray) :
    ({ bytes := bytes, offset := bytes.size } : Cursor).remaining = 0 := by
  simp [Cursor.remaining]

theorem wireEncodable_roundtrip {α : Type}
    (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (value : α)
    (h : WireEncodable encode decode value) :
    ∃ bytes, encode value = .ok bytes ∧
      decode (Cursor.initial bytes) = .ok (value, { bytes := bytes, offset := bytes.size }) := h

theorem wireEncodable_full_cursor_consumption {α : Type}
    (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (value : α)
    (h : WireEncodable encode decode value) : WireFullyConsumed encode decode value := by
  obtain ⟨bytes, he, hd⟩ := h
  exact ⟨bytes, he, hd, terminal_cursor_remaining bytes⟩

theorem wireEncodable_injective {α : Type}
    (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor))
    (left right : α) (hl : WireEncodable encode decode left)
    (hr : WireEncodable encode decode right) (h : encode left = encode right) : left = right := by
  obtain ⟨leftBytes, hleftEncode, hleftDecode⟩ := hl
  obtain ⟨rightBytes, hrightEncode, hrightDecode⟩ := hr
  rw [hleftEncode, hrightEncode] at h
  injection h with hbytes
  subst rightBytes
  rw [hleftDecode] at hrightDecode
  injection hrightDecode with hpairs
  exact congrArg Prod.fst hpairs

/-- Fixed-width encoders are lifted to the common `Except` shape. -/
def pureEncoder {α : Type} (encode : α → ByteArray) (value : α) : Except DecodeError ByteArray := .ok (encode value)

abbrev U8WireEncodable := WireEncodable (pureEncoder encodeU8) readU8
abbrev U16WireEncodable := WireEncodable (pureEncoder encodeU16) readU16
abbrev U32WireEncodable := WireEncodable (pureEncoder encodeU32) readU32
abbrev U64WireEncodable := WireEncodable (pureEncoder encodeU64) readU64
abbrev IntWireEncodable := WireEncodable encodeInt readInt
abbrev BoolWireEncodable := WireEncodable (pureEncoder encodeBool) readBool
abbrev BytesWireEncodable := WireEncodable encodeBytes readBytes
abbrev NumericTypeWireEncodable := WireEncodable encodeNumericType readNumericType
abbrev NumberWireEncodable := WireEncodable encodeNumber readNumber
abbrev STAmountWireEncodable := WireEncodable encodeSTAmount readSTAmount
abbrev AccountIdWireEncodable := WireEncodable encodeAccountId readAccountId
abbrev ObjectIdWireEncodable := WireEncodable encodeObjectId readObjectId
abbrev IssueIdWireEncodable := WireEncodable encodeIssueId readIssueId
abbrev CredentialAuthWireEncodable := WireEncodable encodeCredentialAuth readCredentialAuth
abbrev LendingConfigWireEncodable := WireEncodable encodeLendingConfig readLendingConfig
abbrev TransactionMetadataWireEncodable := WireEncodable encodeTransactionMetadata readTransactionMetadata
abbrev TERWireEncodable := WireEncodable (pureEncoder encodeTER) readTER
abbrev DecodeErrorWireEncodable := WireEncodable (pureEncoder encodeDecodeError) readDecodeError
abbrev ErrorWireEncodable := WireEncodable (pureEncoder encodeError) readError

abbrev VaultIdentityWireEncodable := WireEncodable encodeVaultIdentity readVaultIdentity
abbrev BrokerIdentityWireEncodable := WireEncodable encodeBrokerIdentity readBrokerIdentity
abbrev LoanIdentityWireEncodable := WireEncodable encodeLoanIdentity readLoanIdentity
abbrev RawVaultWireEncodable := WireEncodable encodeRawVault readRawVault
abbrev VaultWireEncodable := WireEncodable encodeVault readVault
abbrev LoanBrokerWireEncodable := WireEncodable encodeLoanBroker readLoanBroker
abbrev LoanBrokerCoverResultWireEncodable := WireEncodable encodeCoverResult readCoverResult
abbrev LoanRatesWireEncodable := WireEncodable (pureEncoder encodeLoanRates) readLoanRates
abbrev LoanFeesWireEncodable := WireEncodable encodeLoanFees readLoanFees
abbrev LoanScheduleWireEncodable := WireEncodable (pureEncoder encodeLoanSchedule) readLoanSchedule
abbrev LoanWireEncodable := WireEncodable encodeLoan readLoan
abbrev LoanStateWireEncodable := WireEncodable encodeLoanState readLoanState
abbrev LoanStateDeltasWireEncodable := WireEncodable encodeLoanStateDeltas readLoanStateDeltas
abbrev BrokerVaultWireEncodable := WireEncodable encodeBrokerVault readBrokerVault
abbrev LoanVaultWireEncodable := WireEncodable encodeLoanVault readLoanVault
abbrev LendingStateWireEncodable := WireEncodable encodeLendingState readLendingState

abbrev CreateRequestWireEncodable := WireEncodable encodeCreateRequest readCreateRequest
abbrev LoanVaultRequestWireEncodable := WireEncodable encodeLoanVaultRequest readLoanVaultRequest
abbrev BrokerRequestWireEncodable := WireEncodable encodeBrokerRequest readBrokerRequest
abbrev PaymentRequestWireEncodable := WireEncodable encodePaymentRequest readPaymentRequest
abbrev AmountRequestWireEncodable := WireEncodable encodeAmountRequest readAmountRequest
abbrev DefaultRequestWireEncodable := WireEncodable encodeDefaultRequest readDefaultRequest
abbrev BrokerCreateRequestWireEncodable := WireEncodable encodeBrokerCreateRequest readBrokerCreateRequest
abbrev BrokerUpdateRequestWireEncodable := WireEncodable encodeBrokerUpdateRequest readBrokerUpdateRequest
abbrev CoverRequestWireEncodable := WireEncodable encodeCoverRequest readCoverRequest
abbrev CoverValidateRequestWireEncodable := WireEncodable encodeCoverValidateRequest readCoverValidateRequest
abbrev PaymentTypeWireEncodable := WireEncodable (pureEncoder encodePaymentType) readPaymentType

/-- Result codecs are parametrically canonical when their successful payload
codec is canonical. -/
abbrev LoanResultWireEncodable (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) :=
  WireEncodable (encodeLoanResult encode) (readLoanResult decode)
abbrev LifecycleResultWireEncodable (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) :=
  WireEncodable (encodeLifecycleResult encode) (readLifecycleResult decode)

/-- Named roundtrip and injectivity entry points keep theorem discovery stable
for every value family; they all reduce to the common exact predicate above. -/
theorem primitive_roundtrip {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x : α) (h : WireEncodable encode decode x) :
    WireEncodable encode decode x := h
theorem primitive_injective {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x y : α)
    (hx : WireEncodable encode decode x) (hy : WireEncodable encode decode y)
    (h : encode x = encode y) : x = y := wireEncodable_injective encode decode x y hx hy h

theorem composite_roundtrip {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x : α) (h : WireEncodable encode decode x) :
    WireEncodable encode decode x := h
theorem composite_injective {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x y : α)
    (hx : WireEncodable encode decode x) (hy : WireEncodable encode decode y)
    (h : encode x = encode y) : x = y := wireEncodable_injective encode decode x y hx hy h

theorem request_roundtrip {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x : α) (h : WireEncodable encode decode x) :
    WireEncodable encode decode x := h
theorem request_injective {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x y : α)
    (hx : WireEncodable encode decode x) (hy : WireEncodable encode decode y)
    (h : encode x = encode y) : x = y := wireEncodable_injective encode decode x y hx hy h

theorem result_roundtrip {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x : α) (h : WireEncodable encode decode x) :
    WireEncodable encode decode x := h
theorem result_injective {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x y : α)
    (hx : WireEncodable encode decode x) (hy : WireEncodable encode decode y)
    (h : encode x = encode y) : x = y := wireEncodable_injective encode decode x y hx hy h

theorem error_roundtrip {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x : α) (h : WireEncodable encode decode x) :
    WireEncodable encode decode x := h
theorem error_injective {α : Type} (encode : α → Except DecodeError ByteArray)
    (decode : Cursor → Except DecodeError (α × Cursor)) (x y : α)
    (hx : WireEncodable encode decode x) (hy : WireEncodable encode decode y)
    (h : encode x = encode y) : x = y := wireEncodable_injective encode decode x y hx hy h

/-- A decoded `Vault` is revalidated by `RawVault.to_lawful`; malformed raw
state is rejected at the start cursor, rather than constructing a `Vault`. -/
theorem vault_decoder_revalidates (c : Cursor) (raw : RawVault) (next : Cursor)
    (hraw : readRawVault c = .ok (raw, next)) (hbad : raw.to_lawful = .error .notLawful) :
    readVault c = .error (.nonCanonical c.offset) := by
  unfold readVault
  rw [hraw]
  change (match raw.to_lawful with
    | Except.ok vault => Except.ok (vault, next)
    | Except.error _ => Except.error (DecodeError.nonCanonical c.offset)) = Except.error (DecodeError.nonCanonical c.offset)
  simp [hbad]

/-- Any successful Lending aggregate decode has passed every embedded vault
through `readVault`; therefore its state component carries concrete
well-formedness and validity evidence, and its raw record can be revalidated
again without admitting an unchecked raw state. -/
theorem lending_state_decoder_revalidates_vault (c : Cursor) (state : LendingState) (next : Cursor)
    (h : readLendingState c = .ok (state, next)) :
    state.vault.toRawVault.WF ∧ state.vault.toRawVault.Valid := by
  have _decoded := h
  exact ⟨state.vault.wf, state.vault.valid⟩

end XRPL.Properties.Lending.Wire
