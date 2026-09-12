import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount

/-! # Proof bodies for the `IntAmount.signum` correctness headlines.

`IntAmount.signum` returns the sign of the value: `1` if positive, `-1` if negative, `0` if
zero. Since `toRat` is the integer cast of `value`, the sign tests reduce to integer sign
tests on `value.toInt`.  -/

namespace XRPL.Model.Protocol

/-- `signum` rewritten with its sign tests on `value.toInt`. -/
private lemma IntAmount.signum_eq_int (x : IntAmount) :
    x.signum = if x.value.toInt < 0 then -1 else if 0 < x.value.toInt then 1 else 0 := by
  have hz : ((0 : Int64)).toInt = 0 := by decide
  have hneg : (x.value < 0) ↔ (x.value.toInt < 0) := by rw [Int64.lt_iff_toInt_lt, hz]
  have hgt : (x.value > 0) ↔ (0 < x.value.toInt) := by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, hz]
  unfold IntAmount.signum
  by_cases h1 : x.value < 0
  · rw [if_pos h1, if_pos (hneg.mp h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (hneg.mpr h))]
    by_cases h2 : x.value > 0
    · rw [if_pos h2, if_pos (hgt.mp h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (hgt.mpr h))]

/-- **`signum` returns the sign of `toRat`.** -/
theorem IntAmount.signum_eq_proof (x : IntAmount) :
    x.signum = if 0 < x.toRat then 1 else if x.toRat < 0 then -1 else 0 := by
  have hpos : (0 < x.toRat) ↔ (0 < x.value.toInt) := by unfold IntAmount.toRat; exact Int.cast_pos
  have hnegR : (x.toRat < 0) ↔ (x.value.toInt < 0) := by unfold IntAmount.toRat; exact Int.cast_lt_zero
  rw [IntAmount.signum_eq_int]
  by_cases h1 : x.value.toInt < 0
  · rw [if_pos h1, if_neg (fun h => absurd (hpos.mp h) (by omega)), if_pos (hnegR.mpr h1)]
  · rw [if_neg h1]
    by_cases h2 : 0 < x.value.toInt
    · rw [if_pos h2, if_pos (hpos.mpr h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (hpos.mp h)), if_neg (fun h => h1 (hnegR.mp h))]

/-- **`signum = 1 ↔ value is positive`.** -/
theorem IntAmount.signum_eq_one_iff_proof (x : IntAmount) : x.signum = 1 ↔ 0 < x.toRat := by
  rw [IntAmount.signum_eq_int,
      show (0 < x.toRat) ↔ (0 < x.value.toInt) from by unfold IntAmount.toRat; exact Int.cast_pos]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

/-- **`signum = -1 ↔ value is negative`.** -/
theorem IntAmount.signum_eq_neg_one_iff_proof (x : IntAmount) : x.signum = -1 ↔ x.toRat < 0 := by
  rw [IntAmount.signum_eq_int,
      show (x.toRat < 0) ↔ (x.value.toInt < 0) from by unfold IntAmount.toRat; exact Int.cast_lt_zero]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

/-- **`signum = 0 ↔ value is zero`.** -/
theorem IntAmount.signum_eq_zero_iff_proof (x : IntAmount) : x.signum = 0 ↔ x.toRat = 0 := by
  rw [IntAmount.signum_eq_int,
      show (x.toRat = 0) ↔ (x.value.toInt = 0) from by unfold IntAmount.toRat; exact Int.cast_eq_zero]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

end XRPL.Model.Protocol
