import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.Number.ToRep.ToRep

/-! # Proof bodies for the `IntAmount` constructor correctness headlines.

`ofInt64` is value-exact; `ofNumber` rounds a `Number` to the nearest integer drops value
(within one), via the `Number` layer's `to_rep`. Mirrors `Number/Constructors/`. The thin
headlines live in `IntAmount.Constructors.Constructors`. -/

namespace XRPL.Model.Protocol

/-- **`ofInt64` is value-exact.** -/
theorem IntAmount.ofInt64_toRat_proof (v : Int64) :
    (IntAmount.ofInt64 v).toRat = (v.toInt : ℚ) := rfl

/-- **`ofNumber` rounds to within one** (it delegates to `Number.to_rep`). -/
theorem IntAmount.ofNumber_within_one_proof (n : Number) (mode : rounding_mode)
    (result : IntAmount) (hn : n.isNormalized)
    (hok : IntAmount.ofNumber n mode = .ok result) :
    |result.toRat - n.toRat| < 1 := by
  unfold IntAmount.ofNumber at hok
  split at hok
  · rename_i rep heq
    have hr : result.toRat = (rep.toInt : ℚ) := by
      rw [← (Except.ok.inj hok)]; rfl
    rw [hr]; exact to_rep_within_one n mode rep hn heq
  · exact absurd hok (by simp)

end XRPL.Model.Protocol
