import XRPL.Model.Protocol.NumericType


namespace XRPL.FFI

open XRPL.Model.Protocol

-- tag: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU). C++ derives it from the asset.
@[export lean_numeric_type_build]
def lean_numeric_type_build (tag : UInt8) : NumericType :=
  match tag.toNat with
  | 0 => .native
  | 1 => .int64
  | _ => .fractional

@[export lean_numeric_type_is_integral]
def lean_numeric_type_is_integral (nt : NumericType) : UInt8 :=
  if nt.isIntegral then 1 else 0

end XRPL.FFI
