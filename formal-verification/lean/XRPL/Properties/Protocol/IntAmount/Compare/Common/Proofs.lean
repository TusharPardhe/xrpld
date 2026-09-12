import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.IntAmount.Common.ToRatLemmas

/-! # Proof bodies for the `IntAmount` comparison headlines (`Compare.Compare`).

Each operator unfolds to its `Int64` `value` comparison, which the `Common.ToRatLemmas`
bridges then identify with the `toRat` order. -/

namespace XRPL.Model.Protocol

/-- **Correctness of `operator_lt`.** -/
theorem IntAmount.operator_lt_iff_proof (x y : IntAmount) :
    IntAmount.operator_lt x y = true ↔ x.toRat < y.toRat := by
  rw [IntAmount.toRat_lt_iff]; unfold IntAmount.operator_lt; exact decide_eq_true_iff

/-- **Correctness of `operator_le`.** -/
theorem IntAmount.operator_le_iff_proof (x y : IntAmount) :
    IntAmount.operator_le x y = true ↔ x.toRat ≤ y.toRat := by
  rw [IntAmount.toRat_le_iff]; unfold IntAmount.operator_le; exact decide_eq_true_iff

/-- **Correctness of `operator_gt`.** -/
theorem IntAmount.operator_gt_iff_proof (x y : IntAmount) :
    IntAmount.operator_gt x y = true ↔ y.toRat < x.toRat := by
  rw [IntAmount.toRat_lt_iff]; unfold IntAmount.operator_gt; exact decide_eq_true_iff

/-- **Correctness of `operator_ge`.** -/
theorem IntAmount.operator_ge_iff_proof (x y : IntAmount) :
    IntAmount.operator_ge x y = true ↔ y.toRat ≤ x.toRat := by
  rw [IntAmount.toRat_le_iff]; unfold IntAmount.operator_ge; exact decide_eq_true_iff

/-- **Correctness of `operator_eq`.** -/
theorem IntAmount.operator_eq_iff_proof (x y : IntAmount) :
    IntAmount.operator_eq x y = true ↔ x.toRat = y.toRat := by
  unfold IntAmount.operator_eq; rw [beq_iff_eq]; exact (IntAmount.toRat_inj x y).symm

/-- **Correctness of `operator_ne`.** -/
theorem IntAmount.operator_ne_iff_proof (x y : IntAmount) :
    IntAmount.operator_ne x y = true ↔ x.toRat ≠ y.toRat := by
  unfold IntAmount.operator_ne; rw [bne_iff_ne]; exact not_congr (IntAmount.toRat_inj x y).symm

/-- **Correctness of `operator_eq_int`.** -/
theorem IntAmount.operator_eq_int_iff_proof (x : IntAmount) (v : Int64) :
    IntAmount.operator_eq_int x v = true ↔ x.toRat = (v.toInt : ℚ) := by
  unfold IntAmount.operator_eq_int; rw [beq_iff_eq]; exact (IntAmount.toRat_eq_int_iff x v).symm

/-- **Correctness of `operator_ne_int`.** -/
theorem IntAmount.operator_ne_int_iff_proof (x : IntAmount) (v : Int64) :
    IntAmount.operator_ne_int x v = true ↔ x.toRat ≠ (v.toInt : ℚ) := by
  unfold IntAmount.operator_ne_int; rw [bne_iff_ne]
  exact not_congr (IntAmount.toRat_eq_int_iff x v).symm

end XRPL.Model.Protocol
