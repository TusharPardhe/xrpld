import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount


namespace XRPL.Model.Protocol

/-- Rational `<` on `toRat` is `Int64` `<` on `value`. -/
lemma IntAmount.toRat_lt_iff (x y : IntAmount) : x.toRat < y.toRat ↔ x.value < y.value := by
  unfold IntAmount.toRat; rw [Int.cast_lt, ← Int64.lt_iff_toInt_lt]

/-- Rational `≤` on `toRat` is `Int64` `≤` on `value`. -/
lemma IntAmount.toRat_le_iff (x y : IntAmount) : x.toRat ≤ y.toRat ↔ x.value ≤ y.value := by
  unfold IntAmount.toRat; rw [Int.cast_le, ← Int64.le_iff_toInt_le]

/-- `toRat` is injective (one-to-one function): equal values iff equal `value`. -/
lemma IntAmount.toRat_inj (x y : IntAmount) : x.toRat = y.toRat ↔ x.value = y.value := by
  unfold IntAmount.toRat; rw [Int.cast_inj, Int64.toInt_inj]

/-- `toRat` equals an `Int64`'s cast iff `value` equals that `Int64`. -/
lemma IntAmount.toRat_eq_int_iff (x : IntAmount) (v : Int64) :
    x.toRat = (v.toInt : ℚ) ↔ x.value = v := by
  unfold IntAmount.toRat; rw [Int.cast_inj, Int64.toInt_inj]

end XRPL.Model.Protocol
