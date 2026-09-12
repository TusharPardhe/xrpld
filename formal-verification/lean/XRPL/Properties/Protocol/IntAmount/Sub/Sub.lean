import XRPL.Properties.Protocol.IntAmount.Sub.Common.Proofs

/-! # Correctness of the `IntAmount` subtraction / negation operators

Each raw `Int64` operation is value-exact (`toRat` of the result equals the rational
operation) as long as the exact integer result stays in the `Int64` range (no overflow). -/

namespace XRPL.Model.Protocol

/-- **`operator_sub` subtracts (no overflow).** -/
theorem IntAmount.operator_sub_exact (x y : IntAmount)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt - y.value.toInt)
    (h_hi : x.value.toInt - y.value.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_sub x y).toRat = x.toRat - y.toRat :=
  IntAmount.operator_sub_exact_proof x y h_lo h_hi

/-- **`operator_neg` negates (overflows only at `minValue`, ruled out by `h_hi`).** -/
theorem IntAmount.operator_neg_exact (x : IntAmount)
    (h_hi : -x.value.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_neg x).toRat = -x.toRat :=
  IntAmount.operator_neg_exact_proof x h_hi

/-- **`operator_sub_int` subtracts an `Int64` (no overflow).** -/
theorem IntAmount.operator_sub_int_exact (x : IntAmount) (v : Int64)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt - v.toInt)
    (h_hi : x.value.toInt - v.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_sub_int x v).toRat = x.toRat - (v.toInt : ℚ) :=
  IntAmount.operator_sub_int_exact_proof x v h_lo h_hi

end XRPL.Model.Protocol
