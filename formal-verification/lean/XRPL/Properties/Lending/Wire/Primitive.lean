import XRPL.FFI.Lending.Wire.Primitive

/-! Foundational verified facts for the canonical Lending wire primitive codec. -/
namespace XRPL.Properties.Lending.Wire

open XRPL.FFI.Lending.Wire

set_option linter.style.nativeDecide false

namespace Primitive

lemma cursor_initial_remaining (bytes : ByteArray) :
    (Cursor.initial bytes).remaining = bytes.size := by
  simp [Cursor.initial, Cursor.remaining]

lemma readU8_encodeU8 (x : UInt8) :
    readU8 (Cursor.initial (encodeU8 x)) = .ok (x, { bytes := encodeU8 x, offset := 1 }) := by
  rfl

/-- Fixed-width little-endian reconstruction facts.  These expose the byte
arithmetic trusted by every composite Lending decoder, without a native
reduction or an external oracle. -/
lemma readU16_encodeU16 (x : UInt16) :
    readU16 (Cursor.initial (encodeU16 x)) = .ok (x, { bytes := encodeU16 x, offset := 2 }) := by
  simp [readU16, Cursor.initial, Cursor.take, encodeU16,
    ByteArray.extract, ByteArray.copySlice, ByteArray.get!]
  bv_decide

lemma readU32_encodeU32 (x : UInt32) :
    readU32 (Cursor.initial (encodeU32 x)) = .ok (x, { bytes := encodeU32 x, offset := 4 }) := by
  simp [readU32, Cursor.initial, Cursor.take, encodeU32,
    ByteArray.extract, ByteArray.copySlice, ByteArray.get!]
  bv_decide

lemma readU64_encodeU64 (x : UInt64) :
    readU64 (Cursor.initial (encodeU64 x)) = .ok (x, { bytes := encodeU64 x, offset := 8 }) := by
  simp [readU64, Cursor.initial, Cursor.take, encodeU64,
    ByteArray.extract, ByteArray.copySlice, ByteArray.get!]
  bv_decide

lemma readBool_encodeBool (x : Bool) :
    readBool (Cursor.initial (encodeBool x)) = .ok (x, { bytes := encodeBool x, offset := 1 }) := by
  cases x <;> rfl

lemma readU8_empty_truncated :
    readU8 (Cursor.initial ByteArray.empty) = .error (.truncated 0 1 0) := by
  rfl

lemma readEnvelope_badMagic :
    readEnvelope 0 (encodeU32 0) = .error .badMagic := by
  rfl

lemma readEnvelope_badVersion :
    readEnvelope 0 (wireMagic ++ one 0) = .error (.badVersion 0) := by
  rfl

lemma readEnvelope_badTag :
    readEnvelope 0 (wireMagic ++ one wireVersion ++ one 1) = .error (.badTag 0 1) := by
  rfl

lemma readEnvelope_trailing :
    readEnvelope 0 (wireMagic ++ one wireVersion ++ one 0 ++ encodeU32 0 ++ one 0) =
      .error (.trailing 10 1) := by
  rfl

lemma readEnvelope_truncated :
    readEnvelope 0 ByteArray.empty = .error (.truncated 0 wireMagic.size 0) := by
  rfl

end Primitive
end XRPL.Properties.Lending.Wire
