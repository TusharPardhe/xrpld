import XRPL.Properties.Protocol.STAmount.Common.IOUWitnessTraces
import XRPL.Properties.Protocol.STAmount.Common.IOUDirectedWitnesses

/-! # Proof body for the IOU multiplication `to_nearest` tightness witness. The thin
headline lives in `Mul.RoundsWithin`. -/

namespace XRPL.Model.Protocol

/-- Proof of `operator_mul_rounds_iou_witness`. -/
theorem STAmount.operator_mul_rounds_iou_witness_proof :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.multiply v1 v2 .fractional .to_nearest = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat * v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  have h1 : (⟨.fractional, 2000000000000001, 0, false⟩ : STAmount).toRat = 2000000000000001 := by
    rw [STAmount.toRat_signed]
    norm_num [show ((2000000000000001 : UInt64).toNat : ℚ) = 2000000000000001 by norm_cast]
  have h2 : (⟨.fractional, 5000000000000000, -15, false⟩ : STAmount).toRat = 5 := by
    rw [STAmount.toRat_signed]
    norm_num [show ((5000000000000000 : UInt64).toNat : ℚ) = 5000000000000000 by norm_cast]
  have hr : (⟨.fractional, 1000000000000000, 1, false⟩ : STAmount).toRat = 10000000000000000 := by
    rw [STAmount.toRat_signed]
    norm_num [show ((1000000000000000 : UInt64).toNat : ℚ) = 1000000000000000 by norm_cast]
  refine ⟨⟨.fractional, 2000000000000001, 0, false⟩, ⟨.fractional, 5000000000000000, -15, false⟩,
          ⟨.fractional, 1000000000000000, 1, false⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          STAmount.multiply_iou_witness_eq, by decide, ?_⟩
  unfold RoundsWithinWitness
  rw [show RatValued.toRat (⟨.fractional, 1000000000000000, 1, false⟩ : STAmount)
        = (⟨.fractional, 1000000000000000, 1, false⟩ : STAmount).toRat from rfl, hr, h1, h2]
  norm_num

end XRPL.Model.Protocol
