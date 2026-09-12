import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.ClawbackReduction
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Vault.Common.ExchangeShared

/-! # `Vault.clawback` accuracy proofs

Proof bodies behind the accuracy headlines in `VaultClawback.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A normalized non-negative `Number` has a clear sign bit. -/
lemma Number.negative_false_of_norm_nonneg (n : Number) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) : n.negative_ = false := by
  rcases hb : n.negative_ with _ | _
  · rfl
  · exfalso
    have hle := Number.toRat_nonpos_of_negative n hb
    have hm0 : n.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp (le_antisymm hle h0)
    exact Number.mantissa_ne_zero_of_negative n hn hb hm0

/-! ## `assetsToSharesWithdraw` accuracy (shares side) -/

/-- **`assetsToSharesWithdraw` prices `assets` into shares within `depositε`.** For
a lawful vault with exact withdraw NAV, a positive exchange-ready `assets` (given
by its exact `toNumber` witness `hanexact` and magnitude floor `hfloor`), and a
nonzero result, there is a `q` (the pre-conversion share `Number`) within
`depositε` of `idealSharesClawback assets`, of which the packed result is either
the floor (`truncateShares`) or a to-nearest whole share. -/
lemma assetsToSharesWithdraw_spec (v : Vault) (assets shares : STAmount)
    (truncateShares : Bool)
    (hnav : v.WithdrawNavExact false)
    (hnn : 0 ≤ assets.toRat)
    (hanexact : ∃ an : Number, assets.toNumber .to_nearest = .ok an ∧
      an.toRat = assets.toRat ∧ an.isNormalized)
    (hfloornz : assets.mValue ≠ 0 → (10 : ℚ) ^ (-81 : ℤ) ≤ |assets.toRat|)
    (hok : assetsToSharesWithdraw v assets truncateShares false = .ok shares)
    (hnz : shares.isZero = false) :
    ∃ q : ℚ, 0 < v.idealSharesClawback assets.toRat ∧
      |q - v.idealSharesClawback assets.toRat|
        ≤ v.idealSharesClawback assets.toRat * depositε ∧
      (match truncateShares with
        | true => shares.toRat = (⌊q⌋ : ℚ)
        | false => |shares.toRat - q| ≤ 1 / 2) ∧
      shares.toRat.den = 1 ∧ 0 ≤ shares.toRat := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false (show (shares.mValue == 0) = false from hnz)
  obtain ⟨nav2, hsub, hcase⟩ :=
    assetsToSharesWithdraw_ok_reduces v assets shares truncateShares false hok
  obtain ⟨netAssetValue, hs, hnavval⟩ := hnav
  have hnav2eq : nav2 = netAssetValue := Except.ok.inj (hsub.symm.trans hs)
  have hnav2val : nav2.toRat = v.withdrawNav := by rw [hnav2eq]; exact hnavval
  rcases hcase with ⟨hzm, hzero⟩ | ⟨hnz2, assetsNumber, sharesAssets, sharesNumber, sharesNumber',
      han, hmul, hdiv, htrunc, hofn⟩
  · exfalso; rw [hzero, STAmount.zero_mValue] at hmv; exact hmv rfl
  have hnav_nn : (0 : ℚ) ≤ v.withdrawNav := by
    unfold RawVault.withdrawNav; exact v.exact.withdraw_nav_nonneg
  have hnav2_pos : 0 < nav2.toRat := by
    have hne : nav2.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero nav2 hnz2
    rw [hnav2val] at hne
    rw [hnav2val]; exact lt_of_le_of_ne hnav_nn (Ne.symm hne)
  have hnav_pos : 0 < v.withdrawNav := by rw [← hnav2val]; exact hnav2_pos
  have hS_pos : 0 < v.sharesTotal.toRat := by
    rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
    · exact h
    · exfalso
      have hz : v.toExact.sharesTotal = 0 := by
        show v.sharesTotal.toRat.num.toNat = 0
        rw [← h]; rfl
      obtain ⟨hAT, hAA⟩ := v.exact.empty_shares hz
      have hle0 : v.withdrawNav ≤ 0 := by
        unfold RawVault.withdrawNav
        rw [hAT]
        have hl := v.exact.lossUnrealized_nonneg
        linarith
      linarith [hnav_pos]
  have hS_one : 1 ≤ v.sharesTotal.toRat := by
    have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hS_pos
    have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
      rw [v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hS_pos.ne'
  obtain ⟨an', han', hanval, hannorm⟩ := hanexact
  have haneq : an' = assetsNumber := by rw [han'] at han; exact Except.ok.inj han
  rw [haneq] at hanval hannorm
  have hnav2norm : nav2.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz v.assetsTotal v.lossUnrealized nav2
      v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hsub
  have hQm : sharesNumber.mantissa_ ≠ 0 := by
    have hsn' : sharesNumber'.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 sharesNumber' .to_nearest shares
        (by decide) hofn hmv
    cases truncateShares with
    | true => exact Number.truncate_source_ne_zero sharesNumber sharesNumber' htrunc hsn'
    | false =>
      have hpure : sharesNumber' = sharesNumber :=
        (Except.ok.inj (show (pure sharesNumber : Except Error Number) = .ok sharesNumber'
          from htrunc)).symm
      rw [hpure] at hsn'; exact hsn'
  -- positivity: a zero input would collapse the product and quotient to zero,
  -- contradicting the nonzero pre-conversion `sharesNumber`
  have hmv0 : assets.mValue ≠ 0 := by
    intro h0
    have habs0 : |assets.toRat| = 0 := by rw [STAmount.abs_toRat, h0]; simp
    have haz : assets.toRat = 0 := abs_eq_zero.mp habs0
    have hanm0 : assetsNumber.mantissa_ = 0 := by
      by_contra hne
      exact Number.toRat_ne_zero_of_mantissa_ne_zero assetsNumber hne (by rw [hanval]; exact haz)
    have hanzero : assetsNumber = Number.zero :=
      Number.eq_zero_of_mantissa_zero assetsNumber hannorm hanm0
    have hSAzero : sharesAssets = Number.zero := by
      rw [hanzero] at hmul
      unfold Number.operator_mul at hmul
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hSm),
          if_pos (show Number.zero.operator_eq Number.zero = true from by decide)] at hmul
      simpa using (Except.ok.inj hmul).symm
    have hSNzero : sharesNumber = Number.zero := by
      rw [hSAzero] at hdiv
      unfold Number.operator_div at hdiv
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hnz2),
          if_pos (show Number.zero.operator_eq Number.zero = true from by decide)] at hdiv
      simpa using (Except.ok.inj hdiv).symm
    rw [hSNzero] at hQm
    exact hQm rfl
  have hfloor : (10 : ℚ) ^ (-81 : ℤ) ≤ |assets.toRat| := hfloornz hmv0
  have hpos : 0 < assets.toRat := by
    have hne : assets.toRat ≠ 0 := by
      intro h; rw [h, abs_zero] at hfloor; exact absurd hfloor (by norm_num)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hApos : 0 < assetsNumber.toRat := by rw [hanval]; exact hpos
  have hAm : assetsNumber.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hApos.ne'
  have hPm : sharesAssets.mantissa_ ≠ 0 := by
    intro h0
    have hsmall := operator_mul_underflow_truth_small v.sharesTotal assetsNumber sharesAssets
      .to_nearest v.wf.sharesTotal_norm hannorm hSm hAm hmul h0
    have hcombo : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
        = (10 : ℚ) ^ (-32750 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num [minExponent]
    rw [hcombo] at hsmall
    have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ |v.sharesTotal.toRat * assetsNumber.toRat| := by
      rw [abs_mul]
      have hh1 : (1 : ℚ) ≤ |v.sharesTotal.toRat| := by rw [abs_of_pos hS_pos]; exact hS_one
      have hh2 : (10 : ℚ) ^ (-81 : ℤ) ≤ |assetsNumber.toRat| := by rw [hanval]; exact hfloor
      nlinarith [abs_nonneg assetsNumber.toRat, abs_nonneg v.sharesTotal.toRat]
    have hmono : (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-81 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    linarith
  obtain ⟨hQnorm, hQpos, hQbound⟩ :=
    RawVault.exchange_pipeline_within v.sharesTotal assetsNumber nav2 sharesAssets sharesNumber
      v.wf.sharesTotal_norm hannorm hnav2norm hS_pos hApos hnav2_pos hmul hdiv hPm hQm
  have hideal_eq : v.sharesTotal.toRat * assetsNumber.toRat / nav2.toRat
      = v.idealSharesClawback assets.toRat := by
    unfold RawVault.idealSharesClawback
    rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, hanval, hnav2val]
  have hideal_pos : 0 < v.idealSharesClawback assets.toRat := by rw [← hideal_eq]; positivity
  rw [hideal_eq] at hQbound
  refine ⟨sharesNumber.toRat, hideal_pos, hQbound, ?_⟩
  have hsnneg : sharesNumber.negative_ = false := Number.negative_false_of_pos sharesNumber hQpos
  cases truncateShares with
  | true =>
    have htr : sharesNumber.truncate = .ok sharesNumber' := htrunc
    obtain ⟨htval, htnorm⟩ := Number.truncate_floor sharesNumber sharesNumber' hQnorm hsnneg htr
    have hsn'm : sharesNumber'.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 sharesNumber' .to_nearest shares
        (by decide) hofn hmv
    have hshval : shares.toRat = sharesNumber'.toRat :=
      STAmount.ofNumber_integral_exact .int64 sharesNumber' .to_nearest shares (by decide)
        (htnorm hsn'm) (by rw [htval]; exact Rat.den_intCast _) hofn
    refine ⟨?_, ?_, ?_⟩
    · show shares.toRat = (⌊sharesNumber.toRat⌋ : ℚ)
      rw [hshval, htval]
    · rw [hshval, htval]; exact Rat.den_intCast _
    · rw [hshval, htval]
      exact_mod_cast Int.floor_nonneg.mpr (le_of_lt hQpos)
  | false =>
    have hpure : sharesNumber' = sharesNumber :=
      (Except.ok.inj (show (pure sharesNumber : Except Error Number) = .ok sharesNumber'
        from htrunc)).symm
    have hofn' : STAmount.ofNumber .int64 sharesNumber .to_nearest = .ok shares := by
      rw [← hpure]; exact hofn
    obtain ⟨hwithin, hden, hnn⟩ :=
      STAmount.ofNumber_int64_to_nearest_within_half sharesNumber shares hQnorm hsnneg hofn'
    exact ⟨hwithin, hden, hnn⟩

/-- **Proof body of `clawback_sharesDestroyed`.** The computed recovery fits under
`assetsAvailable`, so the destroyed shares are priced directly from `assets`. -/
theorem Vault.clawback_sharesDestroyed_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assets.toRat * (1 - depositε) - 1 <
      r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤
      v.idealSharesClawback assets.toRat * (1 + depositε) := by
  obtain ⟨cr, hcomp, herr2, hcrnz, -, hsd_eq, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨hnegf, sd, ar, finalAr, arn2, hsd', has', hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  have hsd_det : sd = sharesDestroyed := by rw [hshares] at hsd'; exact (Except.ok.inj hsd').symm
  have har_det : ar = assetsRecovered := by rw [hsd_det, hassets] at has'; exact (Except.ok.inj has').symm
  have harn_det : arn2 = assetsRecoveredNumber := by
    rw [har_det, hnum] at hnum2; exact (Except.ok.inj hnum2).symm
  rcases hcase with ⟨-, -, -, -, hcrs⟩ | ⟨hgt', -⟩
  · have hrsd : r.sharesDestroyed = sharesDestroyed := by rw [hsd_eq, hcrs, hsd_det]
    have hsdnz : sharesDestroyed.isZero = false := by rw [← hsd_det, ← hcrs]; exact hcrnz
    have hnn : 0 ≤ assets.toRat := by
      rw [STAmount.toRat_of_nonneg assets (show assets.mIsNegative = false from hnegf)]; positivity
    obtain ⟨q, -, hqbound, hmatch, hden, hnn2⟩ :=
      assetsToSharesWithdraw_spec v assets sharesDestroyed true hnav hnn
        (STAmount.toNumber_canonical_exact assets .to_nearest hc)
        (fun hmv => STAmount.Canonical.abs_toRat_ge assets hc hmv) hshares hsdnz
    have hqfloor : sharesDestroyed.toRat = (⌊q⌋ : ℚ) := hmatch
    obtain ⟨hlo_b, hhi_b⟩ := abs_le.mp hqbound
    have hexpand : v.idealSharesClawback assets.toRat * (1 - depositε) =
        v.idealSharesClawback assets.toRat - v.idealSharesClawback assets.toRat * depositε := by ring
    have hexpand' : v.idealSharesClawback assets.toRat * (1 + depositε) =
        v.idealSharesClawback assets.toRat + v.idealSharesClawback assets.toRat * depositε := by ring
    refine ⟨by rw [hrsd]; exact hden, by rw [hrsd]; exact hnn2, ?_, ?_⟩
    · rw [hrsd, hqfloor]
      have hfl : q - 1 < (⌊q⌋ : ℚ) := Int.sub_one_lt_floor q
      linarith [hlo_b, hexpand, hfl]
    · rw [hrsd, hqfloor]
      have hfl : (⌊q⌋ : ℚ) ≤ q := Int.floor_le q
      linarith [hhi_b, hexpand', hfl]
  · rw [harn_det, hle] at hgt'; exact absurd hgt' (by simp)

/-- **Proof body of `clawback_sharesDestroyed_clamped`.** The first computed
recovery exceeds `assetsAvailable`, so the run reprices the truncated share value
of the clamped amount `assetsRecovered' = ofNumber assetsAvailable`, which is a
canonical (nonzero-or-zero) `ofNumber` output priced through the shares side. -/
theorem Vault.clawback_sharesDestroyed_clamped_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered')
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assetsRecovered'.toRat * (1 - depositε) - 1 <
      r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤
      v.idealSharesClawback assetsRecovered'.toRat * (1 + depositε) := by
  obtain ⟨cr, hcomp, herr2, hcrnz, -, hsd_eq, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨-, sd, ar, finalAr, arn2, hsd', has', hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  have hsd_det : sd = sharesDestroyed := by rw [hshares] at hsd'; exact (Except.ok.inj hsd').symm
  have har_det : ar = assetsRecovered := by rw [hsd_det, hassets] at has'; exact (Except.ok.inj has').symm
  have harn_det : arn2 = assetsRecoveredNumber := by
    rw [har_det, hnum] at hnum2; exact (Except.ok.inj hnum2).symm
  rcases hcase with ⟨hgt', -, -, -, -⟩ |
      ⟨-, clamped, sd', ar', finalAr', arn', hclamp', hshareT, -, -, -, -, -, hcr_ar, hcrsd⟩
  · rw [harn_det, hgt] at hgt'; exact absurd hgt' (by simp)
  · have hclamp_det : clamped = assetsRecovered' := by
      rw [hclamped] at hclamp'; exact (Except.ok.inj hclamp').symm
    rw [hclamp_det] at hshareT
    have hrsd : r.sharesDestroyed = sd' := by rw [hsd_eq, hcrsd]
    have hsdnz : sd'.isZero = false := by rw [← hcrsd]; exact hcrnz
    have hAA_neg : v.assetsAvailable.negative_ = false :=
      Number.negative_false_of_norm_nonneg v.assetsAvailable v.wf.assetsAvailable_norm
        v.exact.assetsAvailable_nonneg
    obtain ⟨hnn, hexact, hfloor⟩ :=
      STAmount.ofNumber_input_spec v.numericType v.assetsAvailable .to_nearest assetsRecovered'
        v.wf.assetsAvailable_norm hAA_neg hclamped
    obtain ⟨q, hideal_pos, hqbound, hmatch, hden, hnn2⟩ :=
      assetsToSharesWithdraw_spec v assetsRecovered' sd' true hnav hnn hexact hfloor hshareT hsdnz
    have hqfloor : sd'.toRat = (⌊q⌋ : ℚ) := hmatch
    set ideal : ℚ := v.idealSharesClawback assetsRecovered'.toRat with hideal_def
    obtain ⟨hlo_b, hhi_b⟩ := abs_le.mp hqbound
    have hexpand : ideal * (1 - depositε) = ideal - ideal * depositε := by ring
    have hexpand' : ideal * (1 + depositε) = ideal + ideal * depositε := by ring
    refine ⟨by rw [hrsd]; exact hden, by rw [hrsd]; exact hnn2, ?_, ?_⟩
    · rw [hrsd, hqfloor]
      have hfl : q - 1 < (⌊q⌋ : ℚ) := Int.sub_one_lt_floor q
      linarith [hlo_b, hexpand, hfl]
    · rw [hrsd, hqfloor]
      have hfl : (⌊q⌋ : ℚ) ≤ q := Int.floor_le q
      linarith [hhi_b, hexpand', hfl]


/-- The ideal clawback conversions are algebraic inverses when the NAV and share
supply are nonzero. -/
theorem RawVault.idealAssetsClawback_idealSharesClawback_proof (rv : RawVault) (assets : ℚ)
    (hnav : rv.withdrawNav ≠ 0) (hsh : rv.toExact.sharesTotal ≠ 0) :
    rv.idealAssetsClawback (rv.idealSharesClawback assets) = assets := by
  unfold RawVault.idealAssetsClawback RawVault.idealSharesClawback
  have hsh' : ((rv.toExact.sharesTotal : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsh
  field_simp

/-- A successful nonzero clawback exposes the *raw* share-priced recovery and
its distinct posterior-clamped final recovery. The precision guard is accepted
before the final value is returned. -/
theorem Vault.clawback_raw_final_reduces (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ (sharesDestroyed rawRecovered finalRecovered : STAmount),
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawRecovered ∧
      clampToSumExponent v.assetsTotal rawRecovered.operator_neg = .ok finalRecovered ∧
      finalRecovered.isFractionalNonPositive = .ok false ∧
      r.sharesDestroyed = sharesDestroyed ∧ r.assetsRecovered = finalRecovered := by
  obtain ⟨cr, hcomp, herr2, -, hra, hsd, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨_, ⟨sd, raw, final, _, _, hraw, _, hcase⟩⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  rcases hcase with ⟨-, hclamp, hprecision, hfinal, hshares⟩ |
      ⟨-, _, sd', raw', final', _, _, _, hraw', _, _, hclamp, hprecision, hfinal, hshares⟩
  · exact ⟨sd, raw, final, hraw, hclamp, hprecision, hsd.trans hshares, hra.trans hfinal⟩
  · exact ⟨sd', raw', final', hraw', hclamp, hprecision, hsd.trans hshares, hra.trans hfinal⟩

/-- The zero-amount route has the same posterior raw-to-final recovery order;
the raw conversion starts from the holder's complete share balance. -/
theorem Vault.clawback_raw_final_reduces_zero (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hz : assets.isZero = true)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ (sharesDestroyed rawRecovered finalRecovered : STAmount),
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawRecovered ∧
      clampToSumExponent v.assetsTotal rawRecovered.operator_neg = .ok finalRecovered ∧
      finalRecovered.isFractionalNonPositive = .ok false ∧
      r.sharesDestroyed = sharesDestroyed ∧ r.assetsRecovered = finalRecovered := by
  obtain ⟨cr, hcomp, herr2, -, hra, hsd, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨_, ⟨raw, final, _, hraw, _, hcase⟩⟩ :=
    computeClawback_none_reduces_zero v assets holderShares cr hz hcomp herr2
  rcases hcase with ⟨-, hclamp, hprecision, hfinal, hshares⟩ |
      ⟨-, _, sd', raw', final', _, _, _, hraw', _, _, hclamp, hprecision, hfinal, hshares⟩
  · exact ⟨holderShares, raw, final, hraw, hclamp, hprecision, hsd.trans hshares, hra.trans hfinal⟩
  · exact ⟨sd', raw', final', hraw', hclamp, hprecision, hsd.trans hshares, hra.trans hfinal⟩

/-- The source-faithful recovery contract for a successful nonzero clawback.
The raw share-price is deliberately not identified with the final returned
recovery: the latter is the accepted posterior clamp. -/
theorem Vault.clawback_assetsRecovered_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ (sharesDestroyed rawRecovered finalRecovered : STAmount),
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawRecovered ∧
      clampToSumExponent v.assetsTotal rawRecovered.operator_neg = .ok finalRecovered ∧
      finalRecovered.isFractionalNonPositive = .ok false ∧
      r.sharesDestroyed = sharesDestroyed ∧ r.assetsRecovered = finalRecovered :=
  Vault.clawback_raw_final_reduces v assets holderShares r hznz hok herr

/-- The integral specialization preserves the same execution-order fact; the
integrality assumptions constrain callers but do not justify raw=final. -/
theorem Vault.clawback_assetsRecovered_integral_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnav : v.WithdrawNavExact false) (hint : v.numericType.isIntegral = true)
    (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ (sharesDestroyed rawRecovered finalRecovered : STAmount),
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawRecovered ∧
      clampToSumExponent v.assetsTotal rawRecovered.operator_neg = .ok finalRecovered ∧
      finalRecovered.isFractionalNonPositive = .ok false ∧
      r.sharesDestroyed = sharesDestroyed ∧ r.assetsRecovered = finalRecovered :=
  Vault.clawback_raw_final_reduces v assets holderShares r hznz hok herr

/-- Exact post-success clawback state. The three stored rails are constructed
from the final recovered Number, not from the pre-clamp share-priced recovery. -/
def ClawbackFinalState (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult) : Prop :=
  ∃ cr : ComputeClawbackResult,
    computeClawback v assets holderShares = .ok cr ∧ cr.error = none ∧
    cr.sharesDestroyed.isZero = false ∧
    r.assetsRecovered = cr.assetsRecovered ∧ r.sharesDestroyed = cr.sharesDestroyed ∧
    ∃ (sharesDestroyedNumber assetsRecoveredNumber
        assetsTotal' sharesTotal' assetsAvailable' : Number)
      (assetsTotalRounded assetsTotalRounded' : STAmount),
      cr.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber ∧
      cr.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok assetsTotal' ∧
      STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded ∧
      STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded' ∧
      (assetsRecoveredNumber.mantissa_ != 0 &&
        assetsTotalRounded.operator_eq assetsTotalRounded') = false ∧
      v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok sharesTotal' ∧
      v.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok assetsAvailable' ∧
      r.vault'.toRawVault = { v.toRawVault with sharesTotal := sharesTotal', assetsAvailable := assetsAvailable', assetsTotal := assetsTotal' }

/-- A successful clawback updates all rails from the final recovered Number. -/
theorem Vault.clawback_state_updates_reduces (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ClawbackFinalState v assets holderShares r :=
  Vault.clawback_success_reduces v assets holderShares r hok herr

/-- Public proof body for the exact stored-number update contract. -/
theorem Vault.clawback_vault_updates_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ClawbackFinalState v assets holderShares r :=
  Vault.clawback_state_updates_reduces v assets holderShares r hok herr

/-- The zero-capable state-update contract is identical. -/
theorem Vault.clawback_vault_updates_proof' (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ClawbackFinalState v assets holderShares r :=
  Vault.clawback_state_updates_reduces v assets holderShares r hok herr

/-- Integral callers receive the same exact final-state witnesses. -/
theorem Vault.clawback_vault_updates_integral_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hint : v.numericType.isIntegral = true)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assetsRecovered.toRat) (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    ClawbackFinalState v assets holderShares r :=
  Vault.clawback_state_updates_reduces v assets holderShares r hok herr

end XRPL.Model.SingleAssetVault
