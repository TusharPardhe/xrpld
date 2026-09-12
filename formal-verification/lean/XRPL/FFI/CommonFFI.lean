import XRPL.Model.Protocol.Number

namespace XRPL.FFI

open XRPL.Model.Protocol


@[export lean_rounding_mode_build]
def lean_rounding_mode_build (m : UInt8) : rounding_mode := match m.toNat with
  | 0 => .to_nearest | 1 => .towards_zero | 2 => .downward | _ => .upward

end XRPL.FFI
