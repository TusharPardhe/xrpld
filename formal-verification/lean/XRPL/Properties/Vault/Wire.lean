import XRPL.FFI.Vault.Wire
import XRPL.Properties.Lending.Wire.Canonical
import XRPL.Properties.Vault.Terminal

/-! Exact dispatch, malformed-input atomicity, and canonical codec contracts
for the version-one Vault wire surface.  The module deliberately reuses the
Lending `LWAB` envelope and its canonical codec predicate. -/
namespace XRPL.Properties.Vault.Wire

open XRPL.FFI.Lending.Wire (Cursor DecodeError decodeWhole encodeU32)
open XRPL.FFI.Vault.Wire
open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault
open XRPL.Properties.Lending.Wire (WireEncodable vault_decoder_revalidates)

abbrev BuildRequestWireEncodable := WireEncodable encodeBuildRequest readBuildRequest
abbrev AmountRequestWireEncodable := WireEncodable encodeAmountRequest readAmountRequest
abbrev DonationRequestWireEncodable := WireEncodable encodeDonationRequest readDonationRequest
abbrev WithdrawAmountWireEncodable := WireEncodable encodeWithdrawAmount readWithdrawAmount
abbrev WithdrawRequestWireEncodable := WireEncodable encodeWithdrawRequest readWithdrawRequest
abbrev ClawbackRequestWireEncodable := WireEncodable encodeClawbackRequest readClawbackRequest
abbrev SetRequestWireEncodable := WireEncodable encodeSetRequest readSetRequest
abbrev RoundingResultWireEncodable := WireEncodable encodeRoundingResult readRoundingResult
abbrev DepositResultWireEncodable := WireEncodable encodeDepositResult readDepositResult
abbrev WithdrawResultWireEncodable := WireEncodable encodeWithdrawResult readWithdrawResult
abbrev ClawbackResultWireEncodable := WireEncodable encodeClawbackResult readClawbackResult
abbrev CanBurnResultWireEncodable := WireEncodable encodeCanBurnResult readCanBurnResult

/-- All public wrappers reject any malformed complete request before dispatch. -/
theorem run_decode_failure_atomic
    (requestTag responseTag : UInt8)
    (decode : Cursor → Except DecodeError (α × Cursor))
    (encode : β → Except DecodeError ByteArray)
    (apply : α → β)
    (input : ByteArray) (error : DecodeError)
    (h : decodeWhole requestTag decode input = .error error) :
    run requestTag responseTag decode encode apply input = finish responseTag (.error error) := by
  simp [run, h]

/-- Successful whole-message decoding invokes exactly the named operation and
encodes its complete value (including model error) in the response frame. -/
theorem run_decode_success_exact
    (requestTag responseTag : UInt8)
    (decode : Cursor → Except DecodeError (α × Cursor))
    (encode : β → Except DecodeError ByteArray)
    (apply : α → β)
    (input : ByteArray) (request : α)
    (h : decodeWhole requestTag decode input = .ok request) :
    run requestTag responseTag decode encode apply input = finish responseTag (encode (apply request)) := by
  simp [run, h]

/-- A bad envelope cannot enter any model operation. -/
theorem raw_build_bad_magic_atomic : rawBuildWire (encodeU32 0) = finish 129 (.error .badMagic) := by rfl
theorem build_bad_magic_atomic : buildWire (encodeU32 0) = finish 130 (.error .badMagic) := by rfl
theorem round_deposit_bad_magic_atomic : roundDepositWire (encodeU32 0) = finish 131 (.error .badMagic) := by rfl
theorem deposit_bad_magic_atomic : depositWire (encodeU32 0) = finish 132 (.error .badMagic) := by rfl
theorem quote_withdraw_bad_magic_atomic : sharesToAssetsWithdrawWire (encodeU32 0) = finish 133 (.error .badMagic) := by rfl
theorem withdraw_bad_magic_atomic : withdrawWire (encodeU32 0) = finish 134 (.error .badMagic) := by rfl
theorem clawback_bad_magic_atomic : clawbackWire (encodeU32 0) = finish 135 (.error .badMagic) := by rfl
theorem raw_burn_bad_magic_atomic : burnRawWire (encodeU32 0) = finish 136 (.error .badMagic) := by rfl
theorem burn_bad_magic_atomic : burnWire (encodeU32 0) = finish 137 (.error .badMagic) := by rfl
theorem can_burn_bad_magic_atomic : canBurnWire (encodeU32 0) = finish 138 (.error .badMagic) := by rfl
theorem can_delete_bad_magic_atomic : canDeleteWire (encodeU32 0) = finish 139 (.error .badMagic) := by rfl
theorem can_set_bad_magic_atomic : canSetWire (encodeU32 0) = finish 140 (.error .badMagic) := by rfl

theorem raw_build_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 1 readBuildRequest input = .error error) :
    rawBuildWire input = finish 129 (.error error) := run_decode_failure_atomic 1 129 readBuildRequest encodeVaultResult rawBuild input error h

theorem build_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 2 readBuildRequest input = .error error) :
    buildWire input = finish 130 (.error error) := run_decode_failure_atomic 2 130 readBuildRequest encodeVaultResult terminalBuild input error h

theorem deposit_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 4 readDonationRequest input = .error error) :
    depositWire input = finish 132 (.error error) := run_decode_failure_atomic 4 132 readDonationRequest encodeDepositResultWire (fun r => r.vault.deposit_terminal r.amount r.donation) input error h

theorem withdraw_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 6 readWithdrawRequest input = .error error) :
    withdrawWire input = finish 134 (.error error) := run_decode_failure_atomic 6 134 readWithdrawRequest encodeWithdrawResultWire (fun r => r.vault.withdraw_terminal r.amount r.waiveUnrealizedLoss) input error h

theorem clawback_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 7 readClawbackRequest input = .error error) :
    clawbackWire input = finish 135 (.error error) := run_decode_failure_atomic 7 135 readClawbackRequest encodeClawbackResultWire (fun r => r.vault.clawback_terminal r.assets r.holderShares) input error h

theorem raw_burn_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 8 readAmountRequest input = .error error) :
    burnRawWire input = finish 136 (.error error) := run_decode_failure_atomic 8 136 readAmountRequest encodeVaultResult (fun r => r.vault.burnShares r.amount) input error h

theorem burn_decode_failure_atomic (input : ByteArray) (error : DecodeError)
    (h : decodeWhole 9 readAmountRequest input = .error error) :
    burnWire input = finish 137 (.error error) := run_decode_failure_atomic 9 137 readAmountRequest encodeVaultResult (fun r => r.vault.burnShares_terminal r.amount) input error h

theorem raw_build_decode_success_exact (input : ByteArray) (request : BuildRequest)
    (h : decodeWhole 1 readBuildRequest input = .ok request) :
    rawBuildWire input = finish 129 (encodeVaultResult (rawBuild request)) := by
  simp [rawBuildWire, run, h]

theorem build_decode_success_exact (input : ByteArray) (request : BuildRequest)
    (h : decodeWhole 2 readBuildRequest input = .ok request) :
    buildWire input = finish 130 (encodeVaultResult (terminalBuild request)) := by
  simp [buildWire, run, h]

theorem deposit_decode_success_exact (input : ByteArray) (request : DonationRequest)
    (h : decodeWhole 4 readDonationRequest input = .ok request) :
    depositWire input = finish 132 (encodeDepositResultWire (request.vault.deposit_terminal request.amount request.donation)) := by
  simp [depositWire, run, h]

theorem withdraw_decode_success_exact (input : ByteArray) (request : WithdrawRequest)
    (h : decodeWhole 6 readWithdrawRequest input = .ok request) :
    withdrawWire input = finish 134 (encodeWithdrawResultWire (request.vault.withdraw_terminal request.amount request.waiveUnrealizedLoss)) := by
  simp [withdrawWire, run, h]

theorem clawback_decode_success_exact (input : ByteArray) (request : ClawbackRequest)
    (h : decodeWhole 7 readClawbackRequest input = .ok request) :
    clawbackWire input = finish 135 (encodeClawbackResultWire (request.vault.clawback_terminal request.assets request.holderShares)) := by
  simp [clawbackWire, run, h]

theorem raw_burn_decode_success_exact (input : ByteArray) (request : AmountRequest)
    (h : decodeWhole 8 readAmountRequest input = .ok request) :
    burnRawWire input = finish 136 (encodeVaultResult (request.vault.burnShares request.amount)) := by
  simp [burnRawWire, run, h]

theorem burn_decode_success_exact (input : ByteArray) (request : AmountRequest)
    (h : decodeWhole 9 readAmountRequest input = .ok request) :
    burnWire input = finish 137 (encodeVaultResult (request.vault.burnShares_terminal request.amount)) := by
  simp [burnWire, run, h]

/-- The terminal build wrapper is precisely the single commit-time association
operation, never the raw builder mislabeled as public. -/
theorem terminal_build_has_single_association (request : BuildRequest) :
    terminalBuild request = RawVault.to_lawful_terminal {
      assetsTotal := request.assetsTotal, assetsAvailable := request.assetsAvailable,
      assetsReserved := Number.zero, assetsMaximum := request.assetsMaximum,
      numericType := request.numericType, scale := request.scale,
      sharesTotal := request.sharesTotal, lossUnrealized := request.lossUnrealized } := rfl

/-- Revalidated Vault decoder rejection is inherited by every request decoder
which starts with a full Vault value. -/
theorem vault_request_decoder_revalidates (c : Cursor) (raw : RawVault) (next : Cursor)
    (hraw : XRPL.FFI.Lending.Wire.readRawVault c = .ok (raw, next)) (hbad : raw.to_lawful = .error .notLawful) :
    XRPL.FFI.Lending.Wire.readVault c = .error (.nonCanonical c.offset) :=
  vault_decoder_revalidates c raw next hraw hbad

end XRPL.Properties.Vault.Wire
