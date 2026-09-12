import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Add.Common.RoundsWithinProofs
import XRPL.Properties.Protocol.STAmount.Common.IOUWitnessTraces
import XRPL.Properties.Protocol.STAmount.Common.IOUDirectedWitnesses
import XRPL.Properties.Protocol.IOUAmount.Common.Defs

namespace XRPL.Model.Protocol

/-- Integral (XRP/MPT) addition is exact. -/
theorem STAmount.operator_add_rounds_integral (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hbound_val : v1.mNumericType.maxValue.toNat ≤ maxRep.toNat)
    (hsum : (v1.signedDrops + v2.signedDrops).natAbs < 2 ^ 63)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) :
    RoundsWithin result (v1.toRat + v2.toRat) mode 0 :=
  RoundsWithin_of_eq result (v1.toRat + v2.toRat) mode
    (STAmount.operator_add_integral_exact v1 v2 result mode hc1 hc2 hbound_val hsum hok)

/-- **IOU addition rounds within `IOUAmount.εToNearest`.** -/
theorem STAmount.operator_add_rounds_iou (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 .to_nearest = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .to_nearest IOUAmount.εToNearest :=
  STAmount.operator_add_iou_rel_error v1 v2 result hc1 hc2 h_truth_ne hok hresult

/-- **Tightness witness for the IOU addition bound.** -/
theorem STAmount.operator_add_rounds_iou_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧ v1.toRat + v2.toRat ≠ 0 ∧
      STAmount.operator_add v1 v2 .to_nearest = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  STAmount.operator_add_rounds_iou_witness_proof

/-- **IOU addition, `downward`:  rounding within `IOUAmount.εDirected`.** -/
theorem STAmount.operator_add_rounds_iou_downward (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 .downward = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .downward IOUAmount.εDirected :=
  STAmount.operator_add_iou_rounds_directed v1 v2 result .downward hc1 hc2
    h_truth_ne hok hresult

/-- **IOU addition, `upward`:  rounding within `IOUAmount.εDirected`.** -/
theorem STAmount.operator_add_rounds_iou_upward (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 .upward = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .upward IOUAmount.εDirected :=
  STAmount.operator_add_iou_rounds_directed v1 v2 result .upward hc1 hc2
    h_truth_ne hok hresult

/-- **IOU addition, `towards_zero`: rounding within `IOUAmount.εDirected`.** -/
theorem STAmount.operator_add_rounds_iou_towards_zero (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 .towards_zero = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .towards_zero IOUAmount.εDirected :=
  STAmount.operator_add_iou_rounds_directed v1 v2 result .towards_zero hc1 hc2
    h_truth_ne hok hresult

/-- **Tightness witness, IOU addition `downward`.** -/
theorem STAmount.operator_add_rounds_iou_downward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧ v1.toRat + v2.toRat ≠ 0 ∧
      STAmount.operator_add v1 v2 .downward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  add_dir_wit_core .downward 1000000000000000 (by decide) (Or.inl rfl)

/-- **Tightness witness, IOU addition `upward`.** -/
theorem STAmount.operator_add_rounds_iou_upward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧ v1.toRat + v2.toRat ≠ 0 ∧
      STAmount.operator_add v1 v2 .upward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  add_dir_wit_core .upward 1000000000000001 (by decide) (Or.inr (Or.inl rfl))

/-- **Tightness witness, IOU addition `towards_zero`.** -/
theorem STAmount.operator_add_rounds_iou_towards_zero_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧ v1.toRat + v2.toRat ≠ 0 ∧
      STAmount.operator_add v1 v2 .towards_zero = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  add_dir_wit_core .towards_zero 1000000000000000 (by decide) (Or.inr (Or.inr rfl))

end XRPL.Model.Protocol
