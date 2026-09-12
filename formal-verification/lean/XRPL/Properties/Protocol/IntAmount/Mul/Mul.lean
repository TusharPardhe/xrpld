import XRPL.Properties.Protocol.IntAmount.Mul.Common.Proofs

namespace XRPL.Model.Protocol

/-- **`operator_mul` multiplies by an `Int64` (no overflow).** -/
theorem IntAmount.operator_mul_exact (x : IntAmount) (rhs : Int64)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt * rhs.toInt)
    (h_hi : x.value.toInt * rhs.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_mul x rhs).toRat = x.toRat * (rhs.toInt : ℚ) :=
  IntAmount.operator_mul_exact_proof x rhs h_lo h_hi

end XRPL.Model.Protocol
