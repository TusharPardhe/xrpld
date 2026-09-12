import XRPL.Properties.Protocol.IntAmount.Compare.Common.Proofs

/-! # Correctness of the `IntAmount` comparison operators

`IntAmount` is a single signed `Int64` of drops, so every comparison decides the rational
order of `toRat` exactly and unconditionally. -/

namespace XRPL.Model.Protocol

/-- **`operator_lt` decides `<`.** -/
theorem IntAmount.operator_lt_iff (x y : IntAmount) :
    IntAmount.operator_lt x y = true ↔ x.toRat < y.toRat :=
  IntAmount.operator_lt_iff_proof x y

/-- **`operator_le` decides `≤`.** -/
theorem IntAmount.operator_le_iff (x y : IntAmount) :
    IntAmount.operator_le x y = true ↔ x.toRat ≤ y.toRat :=
  IntAmount.operator_le_iff_proof x y

/-- **`operator_gt` decides `>`.** -/
theorem IntAmount.operator_gt_iff (x y : IntAmount) :
    IntAmount.operator_gt x y = true ↔ y.toRat < x.toRat :=
  IntAmount.operator_gt_iff_proof x y

/-- **`operator_ge` decides `≥`.** -/
theorem IntAmount.operator_ge_iff (x y : IntAmount) :
    IntAmount.operator_ge x y = true ↔ y.toRat ≤ x.toRat :=
  IntAmount.operator_ge_iff_proof x y

/-- **`operator_eq` decides `=`.** -/
theorem IntAmount.operator_eq_iff (x y : IntAmount) :
    IntAmount.operator_eq x y = true ↔ x.toRat = y.toRat :=
  IntAmount.operator_eq_iff_proof x y

/-- **`operator_ne` decides `≠`.** -/
theorem IntAmount.operator_ne_iff (x y : IntAmount) :
    IntAmount.operator_ne x y = true ↔ x.toRat ≠ y.toRat :=
  IntAmount.operator_ne_iff_proof x y

/-- **`operator_eq_int` decides equality with an `Int64`.** -/
theorem IntAmount.operator_eq_int_iff (x : IntAmount) (v : Int64) :
    IntAmount.operator_eq_int x v = true ↔ x.toRat = (v.toInt : ℚ) :=
  IntAmount.operator_eq_int_iff_proof x v

/-- **`operator_ne_int` decides inequality with an `Int64`.** -/
theorem IntAmount.operator_ne_int_iff (x : IntAmount) (v : Int64) :
    IntAmount.operator_ne_int x v = true ↔ x.toRat ≠ (v.toInt : ℚ) :=
  IntAmount.operator_ne_int_iff_proof x v

end XRPL.Model.Protocol
