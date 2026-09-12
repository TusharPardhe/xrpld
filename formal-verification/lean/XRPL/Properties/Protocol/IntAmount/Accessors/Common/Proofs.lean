import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.IntAmount.Common.ToRatLemmas

/-! # Proof bodies for the `IntAmount` accessor correctness headlines. -/

namespace XRPL.Model.Protocol

/-- **`value` is faithful**: the integer cast of `value` is `toRat`. -/
theorem IntAmount.value_toRat_proof (x : IntAmount) :
    ((IntAmount.value x).toInt : ℚ) = x.toRat := rfl

/-- **`toBool` decides non-zeroness.** -/
theorem IntAmount.toBool_iff_proof (x : IntAmount) :
    IntAmount.toBool x = true ↔ x.toRat ≠ 0 := by
  have hz : x.toRat = 0 ↔ x.value = 0 := by
    have h := IntAmount.toRat_eq_int_iff x 0
    rwa [show ((0 : Int64).toInt : ℚ) = 0 from by
      norm_num [show (0 : Int64).toInt = 0 from by decide]] at h
  unfold IntAmount.toBool
  rw [bne_iff_ne, ne_eq, ne_eq, hz]

end XRPL.Model.Protocol
