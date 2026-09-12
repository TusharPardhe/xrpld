import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.Common.AmountArith

/-! # Proof body for the `IntAmount.operator_mul` correctness headline.

`operator_mul` multiplies an `IntAmount` by a raw `Int64` factor (wraps mod 2⁶⁴), so it is
value-exact precisely when the exact integer product stays in the `Int64` range (no
overflow). -/

namespace XRPL.Model.Protocol

/-- **`operator_mul` (by an `Int64`) is value-exact (no overflow).** -/
theorem IntAmount.operator_mul_exact_proof (x : IntAmount) (rhs : Int64)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt * rhs.toInt)
    (h_hi : x.value.toInt * rhs.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_mul x rhs).toRat = x.toRat * (rhs.toInt : ℚ) := by
  unfold IntAmount.operator_mul IntAmount.toRat
  show ((x.value * rhs).toInt : ℚ) = (x.value.toInt : ℚ) * (rhs.toInt : ℚ)
  rw [Int64.toInt_mul, AmountArith.toInt_bmod_self h_lo h_hi]; push_cast; ring

end XRPL.Model.Protocol
