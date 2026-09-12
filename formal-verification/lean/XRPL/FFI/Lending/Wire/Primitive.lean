import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Identity

/-! Canonical version-one Lending wire primitives. -/
namespace XRPL.FFI.Lending.Wire

open XRPL.Model.Protocol
open XRPL.Model.Lending

/-- `LWAB` is the stable Lending wire ABI magic. -/
def wireMagic : ByteArray := [0x4c, 0x57, 0x41, 0x42].toByteArray
def wireVersion : UInt8 := 1
def maxWireBytes : Nat := 65536

inductive DecodeError where
  | truncated (offset needed remaining : Nat)
  | trailing (offset remaining : Nat)
  | badMagic
  | badVersion (actual : UInt8)
  | badTag (expected actual : UInt8)
  | badBoolean (offset : Nat) (actual : UInt8)
  | badOption (offset : Nat) (actual : UInt8)
  | badLength (offset declared : Nat)
  | badNumericType (offset : Nat) (actual : UInt8)
  | outOfRange (offset : Nat)
  | nonCanonical (offset : Nat)
  deriving DecidableEq

structure Cursor where
  bytes : ByteArray
  offset : Nat

namespace Cursor

def initial (bytes : ByteArray) : Cursor := { bytes, offset := 0 }
def remaining (c : Cursor) : Nat := c.bytes.size - c.offset

def take (c : Cursor) (n : Nat) : Except DecodeError (ByteArray × Cursor) :=
  if c.offset + n ≤ c.bytes.size then
    .ok (c.bytes.extract c.offset (c.offset + n), { c with offset := c.offset + n })
  else .error (.truncated c.offset n c.remaining)

def byte (c : Cursor) : Except DecodeError (UInt8 × Cursor) := do
  let (bytes, next) ← c.take 1
  pure (bytes.get! 0, next)

end Cursor

def one (x : UInt8) : ByteArray := [x].toByteArray
def encodeU8 (x : UInt8) : ByteArray := one x
def encodeU16 (x : UInt16) : ByteArray := [x.toUInt8, (x >>> 8).toUInt8].toByteArray
def encodeU32 (x : UInt32) : ByteArray :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8].toByteArray
def encodeU64 (x : UInt64) : ByteArray :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
    (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8].toByteArray

/-- Canonical response payload for a decoder failure.  The first byte is the
failure class; numeric diagnostic fields use fixed little-endian `UInt64`
words. Decoder-produced positions and lengths are bounded by their input. -/
def encodeDecodeError : DecodeError → ByteArray
  | .truncated offset needed remaining =>
    one 0 ++ encodeU64 offset.toUInt64 ++ encodeU64 needed.toUInt64 ++ encodeU64 remaining.toUInt64
  | .trailing offset remaining => one 1 ++ encodeU64 offset.toUInt64 ++ encodeU64 remaining.toUInt64
  | .badMagic => one 2
  | .badVersion actual => one 3 ++ encodeU8 actual
  | .badTag expected actual => one 4 ++ encodeU8 expected ++ encodeU8 actual
  | .badBoolean offset actual => one 5 ++ encodeU64 offset.toUInt64 ++ encodeU8 actual
  | .badOption offset actual => one 6 ++ encodeU64 offset.toUInt64 ++ encodeU8 actual
  | .badLength offset declared => one 7 ++ encodeU64 offset.toUInt64 ++ encodeU64 declared.toUInt64
  | .badNumericType offset actual => one 8 ++ encodeU64 offset.toUInt64 ++ encodeU8 actual
  | .outOfRange offset => one 9 ++ encodeU64 offset.toUInt64
  | .nonCanonical offset => one 10 ++ encodeU64 offset.toUInt64

def readU8 (c : Cursor) : Except DecodeError (UInt8 × Cursor) := c.byte

def readU16 (c : Cursor) : Except DecodeError (UInt16 × Cursor) := do
  let (bytes, next) ← c.take 2
  let value := (bytes.get! 0).toUInt16 ||| ((bytes.get! 1).toUInt16 <<< 8)
  pure (value, next)

def readU32 (c : Cursor) : Except DecodeError (UInt32 × Cursor) := do
  let (bytes, next) ← c.take 4
  let value := (bytes.get! 0).toUInt32 ||| ((bytes.get! 1).toUInt32 <<< 8) |||
    ((bytes.get! 2).toUInt32 <<< 16) ||| ((bytes.get! 3).toUInt32 <<< 24)
  pure (value, next)

def readU64 (c : Cursor) : Except DecodeError (UInt64 × Cursor) := do
  let (bytes, next) ← c.take 8
  let value := (bytes.get! 0).toUInt64 ||| ((bytes.get! 1).toUInt64 <<< 8) |||
    ((bytes.get! 2).toUInt64 <<< 16) ||| ((bytes.get! 3).toUInt64 <<< 24) |||
    ((bytes.get! 4).toUInt64 <<< 32) ||| ((bytes.get! 5).toUInt64 <<< 40) |||
    ((bytes.get! 6).toUInt64 <<< 48) ||| ((bytes.get! 7).toUInt64 <<< 56)
  pure (value, next)

def int64Min : Int := Int64.minValue.toInt
def int64Max : Int := Int64.maxValue.toInt


/-- Decode the exact diagnostic payload emitted by `encodeDecodeError`.
The diagnostic naturals are represented by bounded `UInt64` words, matching
all offsets and lengths produced by the bounded wire reader. -/
def readDecodeError (c : Cursor) : Except DecodeError (DecodeError × Cursor) := do
  let (tag, c) ← readU8 c
  match tag with
  | 0 =>
    let (offset, c) ← readU64 c; let (needed, c) ← readU64 c; let (remaining, c) ← readU64 c
    pure (.truncated offset.toNat needed.toNat remaining.toNat, c)
  | 1 =>
    let (offset, c) ← readU64 c; let (remaining, c) ← readU64 c
    pure (.trailing offset.toNat remaining.toNat, c)
  | 2 => pure (.badMagic, c)
  | 3 => let (actual, c) ← readU8 c; pure (.badVersion actual, c)
  | 4 => let (expected, c) ← readU8 c; let (actual, c) ← readU8 c; pure (.badTag expected actual, c)
  | 5 => let (offset, c) ← readU64 c; let (actual, c) ← readU8 c; pure (.badBoolean offset.toNat actual, c)
  | 6 => let (offset, c) ← readU64 c; let (actual, c) ← readU8 c; pure (.badOption offset.toNat actual, c)
  | 7 => let (offset, c) ← readU64 c; let (declared, c) ← readU64 c; pure (.badLength offset.toNat declared.toNat, c)
  | 8 => let (offset, c) ← readU64 c; let (actual, c) ← readU8 c; pure (.badNumericType offset.toNat actual, c)
  | 9 => let (offset, c) ← readU64 c; pure (.outOfRange offset.toNat, c)
  | 10 => let (offset, c) ← readU64 c; pure (.nonCanonical offset.toNat, c)
  | _ => .error (.badTag 0 tag)
def encodeInt (x : Int) : Except DecodeError ByteArray :=
  if x < int64Min || int64Max < x then .error (.outOfRange 0)
  else .ok (encodeU64 x.toInt64.toUInt64)

def readInt (c : Cursor) : Except DecodeError (Int × Cursor) := do
  let (value, next) ← readU64 c
  pure (value.toInt64.toInt, next)

def encodeBool (x : Bool) : ByteArray := if x then [1].toByteArray else [0].toByteArray
def readBool (c : Cursor) : Except DecodeError (Bool × Cursor) := do
  let start := c.offset
  let (value, next) ← readU8 c
  match value with
  | 0 => pure (false, next)
  | 1 => pure (true, next)
  | _ => .error (.badBoolean start value)

def encodeOption (encode : α → Except DecodeError ByteArray) : Option α → Except DecodeError ByteArray
  | none => .ok [0].toByteArray
  | some value => return [1].toByteArray ++ (← encode value)

def readOption (decode : Cursor → Except DecodeError (α × Cursor))
    (c : Cursor) : Except DecodeError (Option α × Cursor) := do
  let start := c.offset
  let (tag, next) ← readU8 c
  match tag with
  | 0 => pure (none, next)
  | 1 =>
    let (value, final) ← decode next
    pure (some value, final)
  | _ => .error (.badOption start tag)

def encodeBytes (bytes : ByteArray) : Except DecodeError ByteArray :=
  if bytes.size ≤ maxWireBytes then .ok (encodeU32 bytes.size.toUInt32 ++ bytes)
  else .error (.badLength 0 bytes.size)

def readBytes (c : Cursor) : Except DecodeError (ByteArray × Cursor) := do
  let start := c.offset
  let (length, next) ← readU32 c
  let n := length.toNat
  if n ≤ maxWireBytes then next.take n else .error (.badLength start n)

def encodeNumericType : NumericType → Except DecodeError ByteArray
  | .fractional => .ok [0].toByteArray
  | .integral maximum offset sqrt shift => do
    pure ([1].toByteArray ++ encodeU64 maximum ++ (← encodeInt offset) ++ encodeU64 sqrt ++ encodeU64 shift)

def readNumericType (c : Cursor) : Except DecodeError (NumericType × Cursor) := do
  let start := c.offset
  let (tag, c) ← readU8 c
  match tag with
  | 0 => pure (.fractional, c)
  | 1 =>
    let (maximum, c) ← readU64 c
    let (offset, c) ← readInt c
    let (sqrt, c) ← readU64 c
    let (shift, c) ← readU64 c
    pure (.integral maximum offset sqrt shift, c)
  | _ => .error (.badNumericType start tag)

def encodeNumber (x : Number) : Except DecodeError ByteArray :=
  if x.isNormalized then do
    pure (encodeBool x.negative_ ++ encodeU64 x.mantissa_ ++ (← encodeInt x.exponent_))
  else .error (.nonCanonical 0)

def readNumber (c : Cursor) : Except DecodeError (Number × Cursor) := do
  let start := c.offset
  let (negative, c) ← readBool c
  let (mantissa, c) ← readU64 c
  let (exponent, c) ← readInt c
  let value := Number.unchecked negative mantissa exponent
  if value.isNormalized then pure (value, c) else .error (.nonCanonical start)

def encodeSTAmount (x : STAmount) : Except DecodeError ByteArray :=
  match x.canonicalize .to_nearest with
  | .ok canonical =>
    if canonical = x then do
      pure ((← encodeNumericType x.numericType) ++ encodeU64 x.mantissa ++
        (← encodeInt x.exponent) ++ encodeBool x.negative)
    else .error (.nonCanonical 0)
  | .error _ => .error (.nonCanonical 0)

def readSTAmount (c : Cursor) : Except DecodeError (STAmount × Cursor) := do
  let start := c.offset
  let (numericType, c) ← readNumericType c
  let (mantissa, c) ← readU64 c
  let (exponent, c) ← readInt c
  let (negative, c) ← readBool c
  let value := STAmount.unchecked numericType mantissa exponent negative
  match value.canonicalize .to_nearest with
  | .ok canonical => if canonical = value then pure (value, c) else .error (.nonCanonical start)
  | .error _ => .error (.nonCanonical start)

def encodeAccountId (x : AccountId) : Except DecodeError ByteArray := .ok (encodeU64 x.value)
def readAccountId (c : Cursor) : Except DecodeError (AccountId × Cursor) := do
  let (value, c) ← readU64 c
  pure ({ value }, c)

def encodeObjectId (x : ObjectId) : Except DecodeError ByteArray := .ok (encodeU64 x.value)
def readObjectId (c : Cursor) : Except DecodeError (ObjectId × Cursor) := do
  let (value, c) ← readU64 c
  pure ({ value }, c)

def encodeIssueId (x : IssueId) : Except DecodeError ByteArray :=
  return encodeU64 x.currency ++ (← encodeAccountId x.issuer)
def readIssueId (c : Cursor) : Except DecodeError (IssueId × Cursor) := do
  let (currency, c) ← readU64 c
  let (issuer, c) ← readAccountId c
  pure ({ currency, issuer }, c)

def encodeCredentialAuth (x : CredentialAuth) : Except DecodeError ByteArray :=
  .ok (encodeBool x.counterpartySigned ++ encodeBool x.depositAuthorized ++ encodeBool x.credentialAuthorized)
def readCredentialAuth (c : Cursor) : Except DecodeError (CredentialAuth × Cursor) := do
  let (counterpartySigned, c) ← readBool c
  let (depositAuthorized, c) ← readBool c
  let (credentialAuthorized, c) ← readBool c
  pure ({ counterpartySigned, depositAuthorized, credentialAuthorized }, c)

def encodeLendingConfig (x : LendingConfig) : Except DecodeError ByteArray :=
  .ok (encodeBool x.lendingEnabled ++ encodeBool x.singleAssetVaultEnabled ++ encodeU32 x.maximumPaymentsPerTransaction)
def readLendingConfig (c : Cursor) : Except DecodeError (LendingConfig × Cursor) := do
  let (lendingEnabled, c) ← readBool c
  let (singleAssetVaultEnabled, c) ← readBool c
  let (maximumPaymentsPerTransaction, c) ← readU32 c
  pure ({ lendingEnabled, singleAssetVaultEnabled, maximumPaymentsPerTransaction }, c)

def encodeTransactionMetadata (x : TransactionMetadata) : Except DecodeError ByteArray :=
  return (← encodeObjectId x.transactionId) ++ encodeU32 x.sequence ++ encodeU32 x.ledgerCloseTime
def readTransactionMetadata (c : Cursor) : Except DecodeError (TransactionMetadata × Cursor) := do
  let (transactionId, c) ← readObjectId c
  let (sequence, c) ← readU32 c
  let (ledgerCloseTime, c) ← readU32 c
  pure ({ transactionId, sequence, ledgerCloseTime }, c)

def encodeEnvelope (tag : UInt8) (payload : ByteArray) : Except DecodeError ByteArray :=
  return wireMagic ++ encodeU8 wireVersion ++ encodeU8 tag ++ (← encodeBytes payload)

def readEnvelope (expected : UInt8) (input : ByteArray) : Except DecodeError ByteArray := do
  let (magic, c) ← (Cursor.initial input).take wireMagic.size
  if magic != wireMagic then .error .badMagic else
    let (version, c) ← readU8 c
    if version != wireVersion then .error (.badVersion version) else
      let (tag, c) ← readU8 c
      if tag != expected then .error (.badTag expected tag) else
        let (payload, c) ← readBytes c
        if c.remaining = 0 then .ok payload else .error (.trailing c.offset c.remaining)

def decodeWhole (expected : UInt8) (decode : Cursor → Except DecodeError (α × Cursor))
    (input : ByteArray) : Except DecodeError α := do
  let payload ← readEnvelope expected input
  let (value, c) ← decode (Cursor.initial payload)
  if c.remaining = 0 then .ok value else .error (.trailing c.offset c.remaining)

end XRPL.FFI.Lending.Wire
