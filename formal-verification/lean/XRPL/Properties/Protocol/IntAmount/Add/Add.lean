import XRPL.Properties.Protocol.IntAmount.Add.Common.Proofs

namespace XRPL.Model.Protocol

/-- **`operator_add` adds (no overflow).**
- `h_lo`: the exact integer sum is `≥ Int64.minValue` (no underflow);
- `h_hi`: the exact integer sum is `≤ Int64.maxValue` (no overflow).

Safe to assume: `STAmount.canonicalize` rejects native amounts above `kMaxNativeN` on
deserialization, and `kMaxNativeN` is below `Int64.maxValue`. -/
theorem IntAmount.operator_add_exact (x y : IntAmount)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt + y.value.toInt)
    (h_hi : x.value.toInt + y.value.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_add x y).toRat = x.toRat + y.toRat :=
  IntAmount.operator_add_exact_proof x y h_lo h_hi

/-- **`operator_add_int` adds an `Int64` (no overflow).**
- Same hypothesis as operator_add -/
theorem IntAmount.operator_add_int_exact (x : IntAmount) (v : Int64)
    (h_lo : Int64.minValue.toInt ≤ x.value.toInt + v.toInt)
    (h_hi : x.value.toInt + v.toInt ≤ Int64.maxValue.toInt) :
    (IntAmount.operator_add_int x v).toRat = x.toRat + (v.toInt : ℚ) :=
  IntAmount.operator_add_int_exact_proof x v h_lo h_hi

end XRPL.Model.Protocol
