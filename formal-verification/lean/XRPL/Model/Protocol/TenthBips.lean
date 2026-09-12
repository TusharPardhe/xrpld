import XRPL.Model.Protocol.Number

namespace XRPL.Model.Protocol

abbrev TenthBips32 := UInt32

abbrev TenthBips16 := UInt16

def TenthBips32.toNumber (bips : TenthBips32) : Number :=
  Number.ofInt64 bips.toUInt64.toInt64

def TenthBips16.toTenthBips32 (bips : TenthBips16) : TenthBips32 := bips.toUInt32

def kTenthBipsPerUnity : TenthBips32 := ⟨100000⟩

def tenthBipsOfValue (value : Number) (bips : TenthBips32) (mode : rounding_mode)
    : Except Error Number := do
  let rate := bips.toNumber
  let unity := kTenthBipsPerUnity.toNumber
  (← value.operator_mul rate mode).operator_div unity mode

end XRPL.Model.Protocol
