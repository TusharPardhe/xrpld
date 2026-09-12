import XRPL.Properties.Protocol.IntAmount.Accessors.Common.Proofs

namespace XRPL.Model.Protocol

/-- `value` accessor returns exactly `toRat`. -/
theorem IntAmount.value_toRat (x : IntAmount) :
    ((IntAmount.value x).toInt : ℚ) = x.toRat :=
  IntAmount.value_toRat_proof x

/-- `toBool` accessor returns true iff the `toRat` value is not 0. -/
theorem IntAmount.toBool_iff (x : IntAmount) :
    IntAmount.toBool x = true ↔ x.toRat ≠ 0 :=
  IntAmount.toBool_iff_proof x

end XRPL.Model.Protocol
