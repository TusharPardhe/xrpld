import XRPL.Properties.Protocol.STAmount.Add.Common.Integral

namespace XRPL.Model.Protocol

/-! # Integral (XRP/MPT) multiplication exactness -/

/-- For a non-negative offset-0 STAmount, the `UInt64` view of its `signedDrops`
reads back `mValue`. -/
lemma STAmount.signed_toUInt64_toNat (s : STAmount) (hn : s.mIsNegative = false)
    (hlt : s.mValue.toNat < 2 ^ 63) :
    s.signedDrops.toInt64.toUInt64.toNat = s.mValue.toNat := by
  have hsd : s.signedDrops = (s.mValue.toNat : ℤ) := by unfold STAmount.signedDrops; rw [hn]; rfl
  have hexact : s.signedDrops.toInt64.toInt = s.signedDrops :=
    STAmount.signedDrops_toInt64_toInt_of_lt s hlt
  have h0 : (0 : ℤ) ≤ s.signedDrops.toInt64.toInt := by rw [hexact, hsd]; positivity
  have hcast := toUInt64_toNat_of_nonneg s.signedDrops.toInt64 h0
  rw [hexact] at hcast
  have hgoal : (s.signedDrops.toInt64.toUInt64.toNat : ℤ) = (s.mValue.toNat : ℤ) := by
    rw [hcast]; exact hsd
  exact_mod_cast hgoal

/-- For a non-negative offset-0 STAmount, `toRat` is just its `mValue`. -/
lemma STAmount.toRat_of_nonneg_offset_zero (s : STAmount) (hn : s.mIsNegative = false)
    (ho : s.mOffset = 0) : s.toRat = (s.mValue.toNat : ℚ) := by
  rw [STAmount.toRat_of_offset_zero s ho]
  unfold STAmount.signedDrops; rw [hn]; simp

/-- Integral (XRP/MPT) multiplication of two non-negative integral amounts (same
numericType `nt`) whose product is within range is **exact**: -/
theorem STAmount.operator_mul_integral_exact (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hntint : nt.isIntegral = true)
    (hv1nt : v1.mNumericType = nt) (hv2nt : v2.mNumericType = nt)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hbound_val : nt.maxValue.toNat ≤ maxRep.toNat)
    (hbound : v1.mValue.toNat * v2.mValue.toNat ≤ nt.maxValue.toNat)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) :
    result.toRat = v1.toRat * v2.toRat := by
  obtain ⟨hint1, ho1, hb1⟩ := hc1
  obtain ⟨hint2, ho2, hb2⟩ := hc2
  have hmaxlt : maxRep.toNat < 2 ^ 63 := by decide
  have hlt1 : v1.mValue.toNat < 2 ^ 63 := by
    have := hb1; rw [hv1nt] at this; exact lt_of_le_of_lt (le_trans this hbound_val) hmaxlt
  have hlt2 : v2.mValue.toNat < 2 ^ 63 := by
    have := hb2; rw [hv2nt] at this; exact lt_of_le_of_lt (le_trans this hbound_val) hmaxlt
  have htr1 : v1.toRat = (v1.mValue.toNat : ℚ) := STAmount.toRat_of_nonneg_offset_zero v1 hn1 ho1
  have htr2 : v2.toRat = (v2.mValue.toNat : ℚ) := STAmount.toRat_of_nonneg_offset_zero v2 hn2 ho2
  rw [STAmount.multiply] at hok
  by_cases hz : v1.isZero || v2.isZero
  · rw [if_pos hz, STAmount.checked] at hok
    have hchk_int : (STAmount.unchecked nt 0 0 false).integral = true := by
      unfold STAmount.integral STAmount.unchecked; exact hntint
    have h0 := STAmount.canonicalize_integral_toRat _ result mode hchk_int rfl
      (Nat.zero_le _) hok
    rw [h0, STAmount.toRat_zero_aux _ rfl rfl]
    rcases Bool.or_eq_true _ _ |>.mp hz with h | h
    · rw [htr1, show v1.mValue.toNat = 0 from by
        unfold STAmount.isZero at h; rw [beq_iff_eq] at h; rw [h]; rfl]; simp
    · rw [htr2, show v2.mValue.toNat = 0 from by
        unfold STAmount.isZero at h; rw [beq_iff_eq] at h; rw [h]; rfl]; simp
  · have hguard : (v1.integral && v2.integral && nt.isIntegral) = true := by
      simp only [STAmount.integral, hint1, hint2, hntint, Bool.and_self]
    rw [if_neg hz, if_pos hguard] at hok
    set aS : Int64 := v1.signedDrops.toInt64 with haS_def
    set bS : Int64 := v2.signedDrops.toInt64 with hbS_def
    set minV : UInt64 := (if aS ≤ bS then aS else bS).toUInt64 with hminV_def
    set maxV : UInt64 := (if aS ≤ bS then bS else aS).toUInt64 with hmaxV_def
    by_cases hg1 : minV > nt.mulSqrt
    · rw [if_pos hg1] at hok; simp at hok
    rw [if_neg hg1] at hok
    by_cases hg2 : (maxV >>> 32) * minV > nt.mulShift
    · rw [if_pos hg2] at hok; simp at hok
    rw [if_neg hg2, STAmount.checked] at hok
    have haSn : aS.toUInt64.toNat = v1.mValue.toNat := STAmount.signed_toUInt64_toNat v1 hn1 hlt1
    have hbSn : bS.toUInt64.toNat = v2.mValue.toNat := STAmount.signed_toUInt64_toNat v2 hn2 hlt2
    have hminmax : minV.toNat * maxV.toNat = v1.mValue.toNat * v2.mValue.toNat := by
      rw [hminV_def, hmaxV_def]
      by_cases hle : aS ≤ bS
      · rw [if_pos hle, if_pos hle, haSn, hbSn]
      · rw [if_neg hle, if_neg hle, haSn, hbSn, Nat.mul_comm]
    have hprodlt : minV.toNat * maxV.toNat < 2 ^ 64 := by
      have hmr : maxRep.toNat < 2 ^ 64 := by decide
      rw [hminmax]; omega
    have hprodtoNat : (minV * maxV).toNat = v1.mValue.toNat * v2.mValue.toNat := by
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hprodlt, hminmax]
    have hchk_int : (STAmount.unchecked nt (minV * maxV) 0 false).integral = true := by
      unfold STAmount.integral STAmount.unchecked; exact hntint
    have hchk_le : (STAmount.unchecked nt (minV * maxV) 0 false).mValue.toNat ≤ maxRep.toNat := by
      show (minV * maxV).toNat ≤ maxRep.toNat
      rw [hprodtoNat]; exact le_trans hbound hbound_val
    have hcan := STAmount.canonicalize_integral_toRat _ result mode hchk_int rfl hchk_le hok
    rw [hcan, STAmount.toRat_of_nonneg_offset_zero _ rfl rfl]
    show ((STAmount.unchecked nt (minV * maxV) 0 false).mValue.toNat : ℚ) = _
    rw [show (STAmount.unchecked nt (minV * maxV) 0 false).mValue = minV * maxV from rfl,
        hprodtoNat, htr1, htr2]
    push_cast; ring

end XRPL.Model.Protocol
