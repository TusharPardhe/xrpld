import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.Common.AmountArith

/-! # Proof bodies for the `IntAmount` subtraction / negation correctness headlines.

`IntAmount` subtraction and negation are raw signed `Int64` (wraps mod 2⁶⁴), so they are
value-exact precisely when the exact integer result stays in the `Int64` range (no
overflow). The generic no-overflow `bmod` collapse is the shared
`AmountArith.toInt_bmod_self`. The thin headlines live in `IntAmount.Sub.Sub`. -/

namespace XRPL.Model.Protocol

/-- **`operator_sub` is value-exact (no overflow).** -/
theorem IntAmount.operator_sub_exact_proof (x y : IntAmount)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt - y.value.toInt)
    (h_hi : x.value.toInt - y.value.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_sub x y).toRat = x.toRat - y.toRat := by
  unfold IntAmount.operator_sub IntAmount.toRat
  show ((x.value - y.value).toInt : ℚ) = (x.value.toInt : ℚ) - (y.value.toInt : ℚ)
  rw [Int64.toInt_sub, AmountArith.toInt_bmod_self h_lo h_hi]; push_cast; ring

/-- **`operator_neg` is value-exact (overflows only at `minValue`).** The lower bound
`minValue ≤ -x` is automatic (since `x ≤ maxValue < 2⁶³`), so only the upper bound
`-x ≤ maxValue` is required, i.e. `x ≠ minValue`. -/
theorem IntAmount.operator_neg_exact_proof (x : IntAmount)
    (h_hi : -x.value.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_neg x).toRat = -x.toRat := by
  have h_lo : Int64.minValue.toInt ≤ -x.value.toInt := by
    have := Int64.toInt_le x.value
    have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
    have hmax : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
    omega
  unfold IntAmount.operator_neg IntAmount.toRat
  show ((-x.value).toInt : ℚ) = -(x.value.toInt : ℚ)
  rw [Int64.toInt_neg, AmountArith.toInt_bmod_self h_lo h_hi]; push_cast; ring

/-- **`operator_sub_int` is value-exact (no overflow).** -/
theorem IntAmount.operator_sub_int_exact_proof (x : IntAmount) (v : Int64)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt - v.toInt)
    (h_hi : x.value.toInt - v.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_sub_int x v).toRat = x.toRat - (v.toInt : ℚ) := by
  unfold IntAmount.operator_sub_int IntAmount.toRat
  show ((x.value - v).toInt : ℚ) = (x.value.toInt : ℚ) - (v.toInt : ℚ)
  rw [Int64.toInt_sub, AmountArith.toInt_bmod_self h_lo h_hi]; push_cast; ring

end XRPL.Model.Protocol
