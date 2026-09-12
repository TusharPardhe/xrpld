import XRPL.FFI.Lending.Wire.Primitive
import XRPL.FFI.Lending.Wire.Primitive

/-! Kernel-reduced rejection facts for the version-one Lending wire ABI. -/
namespace XRPL.Properties.Lending.Wire

open XRPL.FFI.Lending.Wire

theorem envelope_empty_is_truncated :
    readEnvelope 7 ByteArray.empty = .error (.truncated 0 4 0) := by rfl

theorem envelope_bad_magic_is_rejected :
    readEnvelope 7 ([0, 0, 0, 0].toByteArray) = .error .badMagic := by rfl

theorem envelope_bad_version_is_rejected :
    readEnvelope 7 (wireMagic ++ [2].toByteArray) = .error (.badVersion 2) := by rfl

theorem envelope_bad_tag_is_rejected :
    readEnvelope 7 (wireMagic ++ [wireVersion, 8].toByteArray) = .error (.badTag 7 8) := by rfl

theorem envelope_trailing_is_rejected :
    readEnvelope 7 (wireMagic ++ [wireVersion, 7, 0, 0, 0, 0, 0].toByteArray) =
      .error (.trailing 10 1) := by rfl

theorem bool_noncanonical_is_rejected :
    readBool (Cursor.initial [2].toByteArray) = .error (.badBoolean 0 2) := by rfl

theorem option_noncanonical_is_rejected :
    readOption readU8 (Cursor.initial [2].toByteArray) = .error (.badOption 0 2) := by rfl

theorem numeric_type_noncanonical_is_rejected :
    readNumericType (Cursor.initial [2].toByteArray) = .error (.badNumericType 0 2) := by rfl

theorem encode_int_above_range_is_rejected :
    encodeInt (int64Max + 1) = .error (.outOfRange 0) := by
  simp [encodeInt, int64Max, int64Min]

theorem number_negative_zero_is_rejected :
    readNumber (Cursor.initial (encodeBool true ++ encodeU64 0 ++ encodeU64 0)) =
      .error (.nonCanonical 0) := by rfl

/-- The canonical encoder likewise refuses negative zero, so a universal
unqualified encode/decode identity over all raw `Number` records is false; the
roundtrip domain must require `isNormalized`. -/
theorem encode_number_negative_zero_is_rejected :
    encodeNumber (XRPL.Model.Protocol.Number.unchecked true 0 0) = .error (.nonCanonical 0) := by rfl

end XRPL.Properties.Lending.Wire
