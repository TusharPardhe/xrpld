import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral

namespace XRPL.Model.Protocol

/-! ## Subtraction engines

`operator_sub v1 v2 = operator_add v1 (operator_neg v2)`, so each subtraction
exactness result is the corresponding addition engine applied to the negated
second operand (which stays canonical and keeps its magnitude). -/

/-- Integral (XRP/MPT) subtraction is exact. -/
theorem STAmount.operator_sub_integral_exact (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hbound_val : v1.mNumericType.maxValue.toNat ≤ maxRep.toNat)
    (hsum : (v1.signedDrops - v2.signedDrops).natAbs < 2 ^ 63)
    (hok : STAmount.operator_sub v1 v2 mode = .ok result) :
    result.toRat = v1.toRat - v2.toRat := by
  rw [STAmount.operator_sub] at hok
  have hsum' : (v1.signedDrops + v2.operator_neg.signedDrops).natAbs < 2 ^ 63 := by
    rw [STAmount.operator_neg_signedDrops,
        show v1.signedDrops + -v2.signedDrops = v1.signedDrops - v2.signedDrops from by ring]
    exact hsum
  have hexact := STAmount.operator_add_integral_exact v1 v2.operator_neg result mode
    hc1 hc2.operator_neg hbound_val hsum' hok
  rw [hexact, STAmount.operator_neg_toRat]; ring

end XRPL.Model.Protocol
