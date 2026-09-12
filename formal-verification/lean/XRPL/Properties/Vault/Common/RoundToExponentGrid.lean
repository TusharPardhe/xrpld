import XRPL.Properties.Vault.VaultDeposit
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.RoundCanonical
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.Common.DepositChargeFrac

/-! # Grid-step lower bound for a surviving fractional donation

`roundToVaultExponent` quantizes a fractional deposit onto the grid `10 ^ s` of the
post-deposit total, with `s` the exponent of `ofNumber (assetsTotal + amount)`. This
file packages, for that single `s`, the two facts the donation strict-increase needs:
the surviving amount is at least one grid step (`10 ^ s ≤ rounded`), and the stored
total sits under the 16-digit ceiling of the same scale (`assetsTotal < 2·10^16·10^s`).

The grid-step lower bound splits on `s`: for `s ≥ -81` the exact-floor
characterization (`roundToExponent_rounded`) forces a nonzero floor `≥ 1`; for `s < -81`
the step `10^s` is below the smallest canonical positive `10⁻⁸¹ ≤ rounded`, so it holds
trivially. The stored-total ceiling reads the 16-digit `ofNumber` record's magnitude
(`< 10^16·10^s`) plus its half-ULP `to_nearest` gap, backed off through the `operator_add`
rounding of `assetsTotal + amount`; the flush-to-zero (`ofNumber` mantissa zero) branch
puts the stored total below `10⁻⁸¹`, far under the ceiling. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **Grid-step and ceiling bound for a surviving fractional donation.** For the
post-deposit scale `s`, the surviving rounded amount is at least one grid step
`10 ^ s ≤ rounded`, and the pre-deposit stored total is under `2·10^16·10^s`. -/
lemma Vault.donation_grid_bound (v : Vault)
    (amountDeposit rounded : STAmount)
    (hcanon : amountDeposit.Canonical) (hfr : amountDeposit.integral = false)
    (hpos : 0 < amountDeposit.toRat)
    (hround : roundToVaultExponent amountDeposit v.assetsTotal = .ok rounded)
    (hnz : rounded.isZero = false) :
    ∃ s : ℤ, (10 : ℚ) ^ s ≤ rounded.toRat ∧
      v.assetsTotal.toRat < 2 * 10 ^ 16 * (10 : ℚ) ^ s := by
  set δ : ℚ := 6 / (2 ^ 63 - 3 : ℚ) with hδ_def
  have hδ1 : δ < 1 := by rw [hδ_def]; norm_num
  have hδ0 : (0 : ℚ) ≤ δ := by rw [hδ_def]; norm_num
  have hiou : amountDeposit.IOUCanonical := hcanon.2 hfr
  have hmv : rounded.mValue ≠ 0 := by unfold STAmount.isZero at hnz; exact ne_of_beq_false hnz
  have hrnn : 0 ≤ rounded.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit rounded v.assetsTotal hcanon (le_of_lt hpos) hround
  have hrcanon : rounded.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit rounded v.assetsTotal hcanon hround with hc | hz
    · exact hc
    · rw [hz] at hnz; exact absurd hnz (by decide)
  have hr_ge : (10 : ℚ) ^ (-81 : ℤ) ≤ rounded.toRat := by
    have h := STAmount.Canonical.abs_toRat_ge rounded hrcanon hmv
    rwa [abs_of_nonneg hrnn] at h
  -- peel roundToVaultExponent
  have hround' := hround
  unfold roundToVaultExponent at hround'
  rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hround'
  obtain ⟨_, _, hround'⟩ := bind_ok_peel _ _ _ hround'
  obtain ⟨postScale, hps, hrx⟩ := bind_ok_peel _ _ _ hround'
  -- `roundToVaultExponent` binds `postSumExponent` once, then directly calls
  -- `STAmount.roundToExponent`; unpack the post-sum computation separately.
  unfold postSumExponent at hps
  obtain ⟨amountNumber, hamtN, hps⟩ := bind_ok_peel _ _ _ hps
  obtain ⟨assetsTotal', hAT', hps⟩ := bind_ok_peel _ _ _ hps
  -- amountNumber facts
  obtain ⟨sn, hsn, hsn_val, hsn_norm⟩ := STAmount.toNumber_canonical_exact amountDeposit .to_nearest hcanon
  have haN_eq : amountNumber = sn := Except.ok.inj (hamtN.symm.trans hsn)
  have haN_val : amountNumber.toRat = amountDeposit.toRat := by rw [haN_eq]; exact hsn_val
  have haN_norm : amountNumber.isNormalized := by rw [haN_eq]; exact hsn_norm
  have haN_nn : 0 ≤ amountNumber.toRat := by rw [haN_val]; exact le_of_lt hpos
  have hAnn : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  -- operator_add bound
  have hadd := operator_add_nonneg_rounds v.assetsTotal amountNumber assetsTotal'
    v.wf.assetsTotal_norm haN_norm hAnn haN_nn hAT'
  simp only [RoundsWithin, RatValued.toRat] at hadd
  rw [← hδ_def] at hadd
  have hT_nn : 0 ≤ v.assetsTotal.toRat + amountNumber.toRat := add_nonneg hAnn haN_nn
  rw [abs_of_nonneg hT_nn] at hadd
  have haddle := abs_le.mp hadd
  have hT_pos : 0 < v.assetsTotal.toRat + amountNumber.toRat := by rw [haN_val]; linarith
  have hlb : (v.assetsTotal.toRat + amountNumber.toRat) * (1 - δ) ≤ assetsTotal'.toRat := by
    have hring : (v.assetsTotal.toRat + amountNumber.toRat) * (1 - δ)
        = (v.assetsTotal.toRat + amountNumber.toRat)
          - (v.assetsTotal.toRat + amountNumber.toRat) * δ := by ring
    rw [hring]; linarith [haddle.1]
  have hAlb : v.assetsTotal.toRat * (1 - δ) ≤ assetsTotal'.toRat := by
    have hring2 : v.assetsTotal.toRat * (1 - δ)
        = (v.assetsTotal.toRat + amountNumber.toRat) * (1 - δ) - amountNumber.toRat * (1 - δ) := by ring
    rw [hring2]
    have haN1 : 0 ≤ amountNumber.toRat * (1 - δ) := mul_nonneg haN_nn (by linarith)
    linarith [hlb, haN1]
  -- assetsTotal' > 0, normalized, sign, 19-digit range
  have hAT'_pos : 0 < assetsTotal'.toRat := by
    have hprod : 0 < (v.assetsTotal.toRat + amountNumber.toRat) * (1 - δ) :=
      mul_pos hT_pos (by linarith)
    linarith [hlb, hprod]
  have hAT'_ne : assetsTotal'.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hAT'_pos)
  have hAT'_norm : assetsTotal'.isNormalized :=
    operator_add_isNormalized_to_nearest v.assetsTotal amountNumber assetsTotal'
      v.wf.assetsTotal_norm haN_norm hAT' hAT'_ne
  have hAT'_neg : assetsTotal'.negative_ = false :=
    Number.negative_false_of_norm_nonneg assetsTotal' hAT'_norm (le_of_lt hAT'_pos)
  obtain ⟨hM_lo, hM_hi⟩ := hAT'_norm.mantissaBounds_nat hAT'_ne
  have hE_lo : minExponent ≤ assetsTotal'.exponent_ := by
    rcases hAT'_norm with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show assetsTotal'.mantissa_ = 0 by rw [h0]; rfl) hAT'_ne
    · exact hlo
  -- get `a = ofNumber assetsTotal'`, `postScale = a.exponent`
  have hnum : amountDeposit.numericType = .fractional := hiou.is_fractional
  have hps_frac : numberExponent assetsTotal' .fractional = .ok postScale := by rw [← hnum]; exact hps
  unfold numberExponent at hps_frac
  obtain ⟨a, ha, hae⟩ := bind_ok_peel _ _ _ hps_frac
  have hae' : a.exponent = postScale :=
    Except.ok.inj (show (Except.ok a.exponent : Except Error Int) = .ok postScale from hae)
  by_cases ha_mv : a.mValue = 0
  · -- `ofNumber` flushed to zero: the stored total is below `10⁻⁸¹`, so tiny; take `s = -81`
    have hbelow := STAmount.ofNumber_iou_zero_below_min .fractional assetsTotal' .to_nearest a
      (by decide) hAT'_norm hAT'_neg hAT'_ne ha ha_mv
    refine ⟨-81, hr_ge, ?_⟩
    have hc_pos : (0 : ℚ) < (10 : ℚ) ^ (-81 : ℤ) := zpow_pos (by norm_num) _
    nlinarith [hAlb, hbelow, hc_pos, hAnn, hδ1,
      mul_pos hc_pos (show (0 : ℚ) < 2 * 10 ^ 16 * (1 - δ) - 1 by rw [hδ_def]; norm_num)]
  · -- `ofNumber` is 16-digit canonical: run the grid step and ceiling at `postScale`
    have ha_canon : a.IOUCanonical := by
      rcases STAmount.ofNumber_iou_canonical_or_zero assetsTotal' .to_nearest a hM_lo hM_hi hE_lo ha with hc | hz
      · exact hc
      · exact absurd hz ha_mv
    have hP_pos : (0 : ℚ) < (10 : ℚ) ^ postScale := zpow_pos (by norm_num) _
    have hps_hi : postScale ≤ 80 := by rw [← hae']; exact ha_canon.exp_hi
    refine ⟨postScale, ?_, ?_⟩
    · -- grid step: `10 ^ postScale ≤ rounded`
      by_cases hs81 : (-81 : ℤ) ≤ postScale
      · have hgrid := STAmount.roundToExponent_rounded amountDeposit rounded postScale .downward
          hiou (by omega) hps_hi hmv hrx
        have hval : rounded.toRat = (⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ) * 10 ^ postScale :=
          hgrid
        have hkne : ⌊amountDeposit.toRat / 10 ^ postScale⌋ ≠ 0 := by
          intro h0; rw [h0] at hval; simp only [Int.cast_zero, zero_mul] at hval
          exact (STAmount.toRat_ne_zero rounded hmv) hval
        have hkpos : (0 : ℚ) < amountDeposit.toRat / 10 ^ postScale := div_pos hpos hP_pos
        have hk1 : 1 ≤ ⌊amountDeposit.toRat / 10 ^ postScale⌋ := by
          have hnn : 0 ≤ ⌊amountDeposit.toRat / 10 ^ postScale⌋ := Int.floor_nonneg.mpr (le_of_lt hkpos)
          omega
        have hk1q : (1 : ℚ) ≤ (⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ) := by exact_mod_cast hk1
        rw [hval]; nlinarith [hk1q, hP_pos]
      · push_neg at hs81
        calc (10 : ℚ) ^ postScale ≤ (10 : ℚ) ^ (-81 : ℤ) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ ≤ rounded.toRat := hr_ge
    · -- ceiling: `assetsTotal < 2·10^16·10^postScale`
      have ha_mv' : a.mValue ≠ 0 := ha_mv
      have hsuccess := STAmount.ofNumber_iou_success_exp_range assetsTotal' .to_nearest a
        hM_lo hM_hi hE_lo ha ha_mv'
      obtain ⟨hhalf_bd, hhalf_exp⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional assetsTotal' a
        rfl hM_lo hM_hi hE_lo hsuccess ha ha_mv'
      rw [hae'] at hhalf_exp
      have haoff : a.mOffset = postScale := hae'
      have habs_a : |a.toRat| = (a.mValue.toNat : ℚ) * (10 : ℚ) ^ postScale := by
        rw [STAmount.abs_toRat, haoff]
      have hmant_hi : (a.mValue.toNat : ℚ) < (10 : ℚ) ^ 16 := by
        have := ha_canon.mant_hi; exact_mod_cast this
      have habs_lt : |a.toRat| < (10 : ℚ) ^ 16 * (10 : ℚ) ^ postScale := by
        rw [habs_a]; nlinarith [hP_pos, hmant_hi]
      have hpow_mono : (10 : ℚ) ^ (assetsTotal'.exponent_ + 3) ≤ (10 : ℚ) ^ postScale :=
        zpow_le_zpow_right₀ (by norm_num) hhalf_exp
      have hAT'_ub : assetsTotal'.toRat
          < (10 : ℚ) ^ 16 * (10 : ℚ) ^ postScale + (1 / 2) * (10 : ℚ) ^ postScale := by
        have h1 : assetsTotal'.toRat - a.toRat ≤ |a.toRat - assetsTotal'.toRat| := by
          rw [abs_sub_comm]; exact le_abs_self _
        have h2 : |a.toRat - assetsTotal'.toRat| ≤ (1 / 2) * (10 : ℚ) ^ postScale := by
          apply le_trans hhalf_bd; nlinarith [hpow_mono]
        have h3 : a.toRat ≤ |a.toRat| := le_abs_self _
        linarith [habs_lt, h1, h2, h3]
      have hA_lt : v.assetsTotal.toRat * (1 - δ)
          < (10 : ℚ) ^ 16 * (10 : ℚ) ^ postScale + (1 / 2) * (10 : ℚ) ^ postScale :=
        lt_of_le_of_lt hAlb hAT'_ub
      have hgap : (10 : ℚ) ^ 16 * (10 : ℚ) ^ postScale + (1 / 2) * (10 : ℚ) ^ postScale
          < (2 * 10 ^ 16 * (10 : ℚ) ^ postScale) * (1 - δ) := by
        have hpos2 : 0 < (10 : ℚ) ^ postScale * (2 * 10 ^ 16 * (1 - δ) - (10 ^ 16 + 1 / 2)) :=
          mul_pos hP_pos (by rw [hδ_def]; norm_num)
        nlinarith [hpos2]
      have hmul_ub : v.assetsTotal.toRat * (1 - δ)
          < (2 * 10 ^ 16 * (10 : ℚ) ^ postScale) * (1 - δ) := lt_trans hA_lt hgap
      exact lt_of_mul_lt_mul_right hmul_ub (by linarith : (0 : ℚ) ≤ 1 - δ)

end XRPL.Model.SingleAssetVault
