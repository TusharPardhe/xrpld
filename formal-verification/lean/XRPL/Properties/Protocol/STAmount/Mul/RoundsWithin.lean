-- Multiplication rounding errors, denominated in the ideal product as a rational number

import XRPL.Properties.Protocol.STAmount.Mul.Common.Integral
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Mul.Common.RoundsWithinProofs
import XRPL.Properties.Protocol.STAmount.Common.IOUWitnessTraces
import XRPL.Properties.Protocol.STAmount.Common.IOUDirectedWitnesses

namespace XRPL.Model.Protocol

/-- Relative-error bound for directed-mode IOU multiplication: `Number` multiply
(`10/(2⁶³+2)`) composed with the 16-digit re-round (`10⁻¹⁵`). -/
abbrev εMulIOUDirected : ℚ :=
  10 / (2 ^ 63 + 2 : ℚ) + (10 : ℚ) ^ (-15 : ℤ) + 10 / (2 ^ 63 + 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ)

/-- Relative-error bound for `to_nearest` IOU multiplication: `Number` multiply
(`ε₁ = 5/(2⁶³+7)`) composed with the 16-digit re-round (`ε₂ = ½·10⁻¹⁵`). Both
round-to-nearest (each a half-ULP), so the composed bound is `ε₁ + ε₂ + ε₁·ε₂`.
Half the directed `εMulIOUDirected`. -/
abbrev εMulIOUToNearest : ℚ :=
  5 / (2 ^ 63 + 7 : ℚ) + (1 / 2) * (10 : ℚ) ^ (-15 : ℤ)
    + 5 / (2 ^ 63 + 7 : ℚ) * ((1 / 2) * (10 : ℚ) ^ (-15 : ℤ))

/-- Integral (XRP/MPT) multiplication of two non-negative integral operands (same
numericType `nt`) with in-range product is exact. -/
theorem STAmount.operator_mul_rounds_integral (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hntint : nt.isIntegral = true) (hv1nt : v1.mNumericType = nt) (hv2nt : v2.mNumericType = nt)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hbound_val : nt.maxValue.toNat ≤ maxRep.toNat)
    (hbound : v1.mValue.toNat * v2.mValue.toNat ≤ nt.maxValue.toNat)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) :
    RoundsWithin result (v1.toRat * v2.toRat) mode 0 :=
  RoundsWithin_of_eq result (v1.toRat * v2.toRat) mode
    (STAmount.operator_mul_integral_exact v1 v2 result nt mode hc1 hc2 hntint hv1nt hv2nt
      hn1 hn2 hbound_val hbound hok)

/-- **IOU multiplication rounds within `εMulIOUToNearest`).** -/
theorem STAmount.operator_mul_rounds_iou (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat * v2.toRat) .to_nearest εMulIOUToNearest :=
  STAmount.operator_mul_iou_rel_error v1 v2 result nt hnt hc1 hc2 hok hresult

/-- **Tightness witness for the IOU multiplication bound.** -/
theorem STAmount.operator_mul_rounds_iou_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.multiply v1 v2 .fractional .to_nearest = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat * v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  STAmount.operator_mul_rounds_iou_witness_proof

/-- **IOU multiplication of non-negative operands, `downward`.** -/
theorem STAmount.operator_mul_rounds_iou_downward (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt .downward = .ok result) (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat * v2.toRat) .downward εMulIOUDirected :=
  STAmount.operator_mul_iou_rounds_directed v1 v2 result nt .downward hnt hc1 hc2 hn1 hn2 hok hresult

/-- **IOU multiplication of non-negative operands, `upward`.** -/
theorem STAmount.operator_mul_rounds_iou_upward (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt .upward = .ok result) (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat * v2.toRat) .upward εMulIOUDirected :=
  STAmount.operator_mul_iou_rounds_directed v1 v2 result nt .upward hnt hc1 hc2 hn1 hn2 hok hresult

/-- **IOU multiplication of non-negative operands, `towards_zero`.** -/
theorem STAmount.operator_mul_rounds_iou_towards_zero (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat * v2.toRat) .towards_zero εMulIOUDirected :=
  STAmount.operator_mul_iou_rounds_directed v1 v2 result nt .towards_zero hnt hc1 hc2 hn1 hn2 hok hresult

/-- **Tightness witness, IOU multiplication `downward`.** -/
theorem STAmount.operator_mul_rounds_iou_downward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.multiply v1 v2 .fractional .downward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat * v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  mul_dir_wit_core .downward 1000000000000000 (by decide) (Or.inl rfl)

/-- **Tightness witness, IOU multiplication `upward`.** -/
theorem STAmount.operator_mul_rounds_iou_upward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.multiply v1 v2 .fractional .upward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat * v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  mul_dir_wit_core .upward 1000000000000001 (by decide) (Or.inr (Or.inl rfl))

/-- **Tightness witness, IOU multiplication `towards_zero`.** -/
theorem STAmount.operator_mul_rounds_iou_towards_zero_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.multiply v1 v2 .fractional .towards_zero = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat * v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  mul_dir_wit_core .towards_zero 1000000000000000 (by decide) (Or.inr (Or.inr rfl))

end XRPL.Model.Protocol
