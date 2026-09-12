import XRPL.FFI.Lending.Wire.Transitions

/-! Concrete kernel-checked safety boundaries for the public Lending wire codec. -/
namespace XRPL.Properties.Lending.Wire

open XRPL.FFI.Lending.Wire

/-- Whole-message decoding rejects malformed magic before a payload decoder is reached. -/
theorem decodeWhole_bad_magic_rejected :
    decodeWhole 7 readU8 (encodeU32 0) = .error .badMagic := by rfl

/-- The public Boolean decoder rejects every demonstrated non-canonical tag. -/
theorem readBool_tag_two_rejected :
    readBool (Cursor.initial [2].toByteArray) = .error (.badBoolean 0 2) := by rfl

/-- The public option decoder rejects every demonstrated non-canonical tag. -/
theorem readOption_tag_two_rejected :
    readOption readU8 (Cursor.initial [2].toByteArray) = .error (.badOption 0 2) := by rfl

/-- The public numeric-type decoder rejects every demonstrated non-canonical tag. -/
theorem readNumericType_tag_two_rejected :
    readNumericType (Cursor.initial [2].toByteArray) = .error (.badNumericType 0 2) := by rfl

/-- A canonical `Number` decoder refuses negative zero before any Vault
revalidation can begin. -/
theorem readNumber_negative_zero_rejected :
    readNumber (Cursor.initial (encodeBool true ++ encodeU64 0 ++ encodeU64 0)) =
      .error (.nonCanonical 0) := by rfl

end XRPL.Properties.Lending.Wire
