import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.Common.AmountArith

/-! # Proof bodies for the `IntAmount` addition correctness headlines.

`IntAmount` addition is raw signed `Int64` (wraps mod 2⁶⁴), so it is value-exact precisely
when the exact integer sum stays in the `Int64` range (no overflow). The generic no-overflow
`bmod` collapse is the shared `AmountArith.toInt_bmod_self`. The thin headlines live in
`IntAmount.Add.Add`. -/

namespace XRPL.Model.Protocol

/-- **`operator_add` is value-exact (no overflow).** -/
theorem IntAmount.operator_add_exact_proof (x y : IntAmount)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt + y.value.toInt)
    (h_hi : x.value.toInt + y.value.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_add x y).toRat = x.toRat + y.toRat := by
  unfold IntAmount.operator_add IntAmount.toRat
  show ((x.value + y.value).toInt : ℚ) = (x.value.toInt : ℚ) + (y.value.toInt : ℚ)
  rw [Int64.toInt_add, AmountArith.toInt_bmod_self h_lo h_hi]; push_cast; ring

/-- **`operator_add_int` is value-exact (no overflow).** -/
theorem IntAmount.operator_add_int_exact_proof (x : IntAmount) (v : Int64)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt + v.toInt)
    (h_hi : x.value.toInt + v.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_add_int x v).toRat = x.toRat + (v.toInt : ℚ) := by
  unfold IntAmount.operator_add_int IntAmount.toRat
  show ((x.value + v).toInt : ℚ) = (x.value.toInt : ℚ) + (v.toInt : ℚ)
  rw [Int64.toInt_add, AmountArith.toInt_bmod_self h_lo h_hi]; push_cast; ring

end XRPL.Model.Protocol
