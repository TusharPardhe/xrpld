import XRPL.Properties.Protocol.IntAmount.Constructors.Common.Proofs

/-! # Correctness of the `IntAmount` constructors -/

namespace XRPL.Model.Protocol

/-- **`ofInt64` is value-exact.** -/
theorem IntAmount.ofInt64_toRat (v : Int64) :
    (IntAmount.ofInt64 v).toRat = (v.toInt : ℚ) :=
  IntAmount.ofInt64_toRat_proof v

/-- **`ofNumber` converts a `Number` to integer drops, off by less than one drop.** -/
theorem IntAmount.ofNumber_within_one (n : Number) (mode : rounding_mode)
    (result : IntAmount) (hn : n.isNormalized)
    (hok : IntAmount.ofNumber n mode = .ok result) :
    |result.toRat - n.toRat| < 1 :=
  IntAmount.ofNumber_within_one_proof n mode result hn hok

end XRPL.Model.Protocol
