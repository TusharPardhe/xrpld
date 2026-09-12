-- Multiplication rounding errors, denominated in computed-value ULP increments

import XRPL.Properties.Protocol.STAmount.Mul.Common.Integral
import XRPL.Properties.Protocol.STAmount.Mul.Common.RoundsToRepresentableProofs

namespace XRPL.Model.Protocol

/-! # Multiplication, discrete/ULP -/

/-- Integral (XRP/MPT) multiplication is exact. -/
theorem STAmount.operator_mul_repr_integral (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hntint : nt.isIntegral = true) (hv1nt : v1.mNumericType = nt) (hv2nt : v2.mNumericType = nt)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hbound_val : nt.maxValue.toNat ≤ maxRep.toNat)
    (hbound : v1.mValue.toNat * v2.mValue.toNat ≤ nt.maxValue.toNat)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) :
    |result.toRat - v1.toRat * v2.toRat| = 0 := by
  simp [STAmount.operator_mul_integral_exact v1 v2 result nt mode hc1 hc2 hntint hv1nt hv2nt
    hn1 hn2 hbound_val hbound hok]

/-- **IOU multiplication lands within `1` ULP of `v1 · v2` (`to_nearest`).** -/
theorem STAmount.operator_mul_repr_iou (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ 10 ^ result.exponent :=
  STAmount.operator_mul_repr_iou_proof v1 v2 result nt hnt hc1 hc2 hok hresult

/-- **IOU multiplication of non-negative operands lands within `1` ULP of `v1 · v2`
(directed modes), on the correct side.** -/
theorem STAmount.operator_mul_repr_iou_directed (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
  (mode = .downward → result.toRat ≤ v1.toRat * v2.toRat) ∧
  (mode = .upward → v1.toRat * v2.toRat ≤ result.toRat) ∧
  |result.toRat - v1.toRat * v2.toRat| ≤ 10 ^ result.exponent :=
  STAmount.operator_mul_repr_iou_directed_proof v1 v2 result nt mode hnt
    hc1 hc2 hn1 hn2 hok hresult

/-- **IOU multiplication is accurate to `1` ULP, any operand signs, any mode.**
Magnitude bound only; the directional side-claim needs non-negative operands
(`operator_mul_repr_iou_directed`). -/
theorem STAmount.operator_mul_iou_within_1ulp (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ 10 ^ result.exponent :=
  STAmount.operator_mul_iou_within_1ulp_proof v1 v2 result nt mode hnt
    hc1 hc2 hok hresult

/-- **IOU multiplication lands within `1` ULP of `v1 · v2` (`towards_zero`), any sign.**
Truncation needs no sign restriction, unlike the other directed modes. -/
theorem STAmount.operator_mul_repr_iou_towards_zero (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ 10 ^ result.exponent :=
  STAmount.operator_mul_iou_towards_zero_one v1 v2 result nt hnt
    hc1 hc2 hok hresult

/-- **IOU multiplication never increases magnitude (`towards_zero`), any sign.**
`upward`/`downward` admit no such any-sign directional statement. -/
theorem STAmount.operator_mul_iou_abs_le_towards_zero (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat| ≤ |v1.toRat * v2.toRat| :=
  STAmount.operator_mul_iou_abs_le_towards_zero_proof v1 v2 result nt hnt
    hc1 hc2 hok hresult

end XRPL.Model.Protocol
