import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.WithdrawExits
import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.DepositChargeProofs
import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Vault.Common.ExchangeShared
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical

/-! # `Vault.sharesToAssetsWithdraw` / `Vault.withdraw` accuracy proof bodies

Proof bodies behind the accuracy headlines in `VaultWithdraw.lean` that need the
directed-`ofNumber` boundary lemmas (`OfNumberBoundary`) and the deposit exchange
pipeline machinery (`DepositAccuracy`, `DepositChargeProofs`). Those files import
`WithdrawAccuracy`, so these bodies cannot live there and are collected here
instead. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Downward `ofNumber` is the floor within one ULP -/

/-- **`.downward` `ofNumber` floors within one ULP.** For a normalized sign-cleared
`Number` `n` whose conversion into `nt` lands on a nonzero record, the result never
exceeds `n`, sits within `10 ^ result.exponent` below it, and is non-negative. Both
the integral (`to_rep` floor, exponent `0`) and fractional (16-digit downward snap)
paths obey this. -/
lemma STAmount.ofNumber_downward_floor_bounds (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hres : result.mValue ≠ 0) :
    result.toRat ≤ n.toRat ∧
    n.toRat - result.toRat ≤ (10 : ℚ) ^ result.exponent ∧
    0 ≤ result.toRat := by
  by_cases hint : nt.isIntegral = true
  · -- integral: `to_rep .downward` is the floor, result exponent is `0`
    unfold STAmount.ofNumber at hok
    simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
    cases hr : n.to_rep .downward with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok intValue =>
      rw [hr] at hok
      simp only [] at hok
      obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n .downward intValue hneg hr
      have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep intValue hnn hle
      have hres_val : result.toRat = (intValue.toInt : ℚ) := by
        have hexact := STAmount.canonicalize_integral_toRat
          (STAmount.unchecked nt intValue.toUInt64 0 false) result .downward
          (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
          hval hok
        rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
        show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
        rw [toUInt64_toNat_of_nonneg intValue hnn]
      have hres_exp : result.exponent = 0 := by
        obtain ⟨_, hoff, _⟩ := STAmount.canonicalize_integral_facts
          (STAmount.unchecked nt intValue.toUInt64 0 false) result .downward
          (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint)
          rfl hval hok
        exact hoff
      obtain ⟨hfl_le, hfl_lt⟩ := Number.to_rep_downward_floor n intValue hn hneg hr
      refine ⟨by rw [hres_val]; exact hfl_le, ?_, by rw [hres_val]; exact_mod_cast hnn⟩
      rw [hres_val, hres_exp, zpow_zero]
      linarith [hfl_lt]
  · -- fractional: the 16-digit downward snap is within one 16-digit ULP below
    have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    have hn_ne : n.mantissa_ ≠ 0 :=
      STAmount.ofNumber_iou_mantissa_ne_zero nt n .downward result hnt_frac hok hres
    obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
      · exact hlo
    have hok' : STAmount.ofNumber .fractional n .downward = .ok result := by
      rw [← hnt_frac]; exact hok
    have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
      STAmount.ofNumber_iou_success_exp_range n .downward result hlo19 hhi19 hexp_lo hok' hres
    have hrw := STAmount.ofNumber_iou_rounds_within nt n .downward result hnt_frac hneg
      hlo19 hhi19 hexp_lo hexp_hi hok hres
    obtain ⟨hle, -⟩ := hrw
    have hle' : result.toRat ≤ n.toRat := hle
    obtain ⟨hulp, hexp_ge⟩ := STAmount.ofNumber_iou_within_ulp nt n .downward result hnt_frac
      hlo19 hhi19 hexp_lo hexp_hi hok hres
    have hnonneg : 0 ≤ result.toRat := by
      obtain ⟨mant, exp, -, hval, -, hcast, -, -, -, -⟩ :=
        STAmount.ofNumber_iou_snap_pos nt n .downward result hnt_frac hneg
          hlo19 hhi19 hexp_lo hexp_hi hok hres
      rw [hval, hcast]; positivity
    refine ⟨hle', ?_, hnonneg⟩
    have hgap : n.toRat - result.toRat ≤ (10 : ℚ) ^ (n.exponent_ + 3) := by
      have h1 : n.toRat - result.toRat = |result.toRat - n.toRat| := by
        rw [abs_of_nonpos (by linarith [hle'] : result.toRat - n.toRat ≤ 0)]; ring
      rw [h1]; exact hulp
    calc n.toRat - result.toRat ≤ (10 : ℚ) ^ (n.exponent_ + 3) := hgap
      _ ≤ (10 : ℚ) ^ result.exponent := zpow_le_zpow_right₀ (by norm_num) hexp_ge

/-! ## Pipeline closure for the two-stage `mul`/`div` withdraw exchange -/

/-- Upper closure of the exact-`nav` `mul`/`div` withdraw pipeline within `depositε`. -/
lemma withdraw_pipeline_up :
    ((1 : ℚ) + 5 / (2 ^ 63 + 7)) * (1 + 6 / (2 ^ 63 - 3)) ≤ (1 + depositε) * (1 - 0) := by
  rw [depositε_eq]; norm_num

/-- Lower closure of the exact-`nav` `mul`/`div` withdraw pipeline within `depositε`. -/
lemma withdraw_pipeline_lo :
    ((1 : ℚ) - depositε) * (1 + 0) ≤ (1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3)) := by
  rw [depositε_eq]; norm_num

/-! ## `sharesToAssetsWithdraw` value specification -/

/-- **Value specification of `sharesToAssetsWithdraw`.** On a lawful vault with an
exact pricing net asset value, the returned amount is non-negative, never exceeds
the shares' worth by more than `depositε` relatively, and when nonzero falls short
of it by at most the interior stage error plus one ULP: the pricing collapses to
the exact `nav`, the `mul`/`div` stages round within `depositε`, and the final
`.downward` `ofNumber` floors within one ULP. -/
theorem Vault.sharesToAssetsWithdraw_spec (v : Vault)
    (shares assets : STAmount) (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    0 ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat ∧
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) ∧
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε +
          (10 : ℚ) ^ assets.exponent) := by
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hεlt : depositε < 1 := by rw [depositε_eq]; norm_num
  -- reduce the run and collapse the two subtractions to the exact `nav`
  obtain ⟨nav2, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waiveUnrealizedLoss hok
  have hnav2facts : nav2.isNormalized ∧
      nav2.toRat = (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    obtain ⟨nv, he, heval⟩ := hnav
    cases waiveUnrealizedLoss with
    | false =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm
        v.wf.lossUnrealized_norm hsub, by rw [hval]; exact heval⟩
    | true =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub,
        by rw [hval]; exact heval⟩
  obtain ⟨hnav2norm, hnav2_val⟩ := hnav2facts
  -- `nav` is non-negative on a lawful vault
  have hnav_nonneg : 0 ≤ (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    cases waiveUnrealizedLoss with
    | false =>
      rw [if_neg (by decide)]
      show 0 ≤ v.withdrawNav
      unfold RawVault.withdrawNav; exact v.exact.withdraw_nav_nonneg
    | true =>
      rw [if_pos rfl]
      show 0 ≤ v.depositNav
      unfold RawVault.depositNav
      exact v.exact.assetsTotal_nonneg
  set nav : ℚ := (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) with hnav_def
  rcases hcase with ⟨hnav2m, hzero⟩ |
      ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · -- zero net asset value: the payout is the canonical zero, the ideal is `0`
    subst hzero
    have hnav0 : nav = 0 := by
      have h : nav2.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero nav2 hnav2m
      linarith [hnav2_val]
    have hideal0 : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat = 0 := by
      show nav * shares.toRat / (v.toExact.sharesTotal : ℚ) = 0
      rw [hnav0]; ring
    have haz : (STAmount.zero v.numericType).toRat = 0 := STAmount.zero_toRat v.numericType
    rw [hideal0]
    refine ⟨by rw [haz], le_refl 0, by rw [haz, zero_mul], ?_⟩
    intro hf
    rw [STAmount.zero_isZero] at hf
    exact absurd hf (by decide)
  · -- genuine pricing: run the relative composition, then the downward floor
    set ST : ℚ := (v.toExact.sharesTotal : ℚ) with hST_def
    have hST_eq : ST = v.sharesTotal.toRat := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hideal_eq : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat = nav * shares.toRat / ST := rfl
    obtain ⟨sn0, hsn0ok, hsn0val, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsn_eq : sn0 = sharesNumber := by rw [hsn0ok] at hsn; exact Except.ok.inj hsn
    have hsnnorm : sharesNumber.isNormalized := by rw [← hsn_eq]; exact hsn0norm
    have hsnval : sharesNumber.toRat = shares.toRat := by rw [← hsn_eq]; exact hsn0val
    -- `nav` positive: nonzero pricing forces a nonzero mantissa
    have hnav2_ne0 : nav2.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero nav2 hnav2m
    have hnav_pos : 0 < nav := by
      rcases lt_or_eq_of_le hnav_nonneg with h | h
      · exact h
      · exact absurd (by linarith [hnav2_val] : nav2.toRat = 0) hnav2_ne0
    -- shares total positive
    have hApos : 0 < v.toExact.assetsTotal := by
      have hle : nav ≤ v.toExact.assetsTotal := by
        rw [hnav_def]
        cases waiveUnrealizedLoss with
        | true =>
          rw [if_pos rfl]; show v.depositNav ≤ _; unfold RawVault.depositNav
          linarith
        | false =>
          rw [if_neg (by decide)]; show v.withdrawNav ≤ _; unfold RawVault.withdrawNav
          linarith [v.exact.lossUnrealized_nonneg]
      linarith
    have hST_pos : 0 < ST := by
      rw [hST_def]
      have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
        absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hSTne : v.sharesTotal.toRat ≠ 0 := hST_eq ▸ ne_of_gt hST_pos
    have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero hSTne
    -- decide the output shape
    by_cases hzf : assets.isZero = false
    · -- nonzero payout: full pipeline plus downward floor
      have hres_ne : assets.mValue ≠ 0 := ne_of_beq_false hzf
      have hanm : assetsNumber.mantissa_ ≠ 0 :=
        STAmount.ofNumber_source_ne_zero v.numericType assetsNumber .downward assets hof hres_ne
      have hNAVm : NAVShares.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hdiv hanm
      obtain ⟨hnav2_m', hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
      have hNAVnorm : NAVShares.isNormalized :=
        operator_mul_result_isNormalized nav2 sharesNumber NAVShares .to_nearest
          hnav2norm hsnnorm hnav2m hsn_m hmul hNAVm
      have hshares_pos : 0 < shares.toRat := by
        have hsnne : sharesNumber.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero sharesNumber hsn_m
        rw [hsnval] at hsnne
        exact lt_of_le_of_ne hnn (Ne.symm hsnne)
      set T0 : ℚ := nav * shares.toRat with hT0_def
      have hT0_pos : 0 < T0 := mul_pos hnav_pos hshares_pos
      have hANnorm : assetsNumber.isNormalized :=
        operator_div_result_isNormalized NAVShares v.sharesTotal assetsNumber .to_nearest
          hNAVnorm v.wf.sharesTotal_norm hNAVm hSTm hdiv hanm
      -- stage bounds
      have hmulb : |NAVShares.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
        have hmulraw : |NAVShares.toRat - nav2.toRat * sharesNumber.toRat| ≤
            |nav2.toRat * sharesNumber.toRat| * (5 / (2 ^ 63 + 7)) :=
          operator_mul_rounds_to_nearest nav2 sharesNumber NAVShares hnav2norm hsnnorm hmul hNAVm
        have hval : nav2.toRat * sharesNumber.toRat = T0 := by
          rw [hT0_def, hnav2_val, hsnval]
        rwa [hval, abs_of_pos hT0_pos] at hmulraw
      have hε₂lt : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      have hε₃lt : (6 : ℚ) / (2 ^ 63 - 3) < 1 := by norm_num
      have hNAVpos : 0 < NAVShares.toRat := by
        have := abs_le.mp hmulb; nlinarith [hT0_pos]
      have hAN_ST_pos : 0 < NAVShares.toRat / ST := div_pos hNAVpos hST_pos
      have hdivb : |assetsNumber.toRat - NAVShares.toRat / ST| ≤
          NAVShares.toRat / ST * (6 / (2 ^ 63 - 3)) := by
        have h : |assetsNumber.toRat - NAVShares.toRat / v.sharesTotal.toRat| ≤
            |NAVShares.toRat / v.sharesTotal.toRat| * (6 / (2 ^ 63 - 3)) :=
          operator_div_rounds_to_nearest NAVShares v.sharesTotal assetsNumber
            hNAVnorm v.wf.sharesTotal_norm hdiv hanm
        rw [← hST_eq] at h
        rwa [abs_of_pos hAN_ST_pos] at h
      have hANpos : 0 < assetsNumber.toRat := by
        have := abs_le.mp hdivb; nlinarith [hAN_ST_pos]
      have h3 : |assetsNumber.toRat * ST - NAVShares.toRat| ≤ NAVShares.toRat * (6 / (2 ^ 63 - 3)) := by
        have hrw : assetsNumber.toRat * ST - NAVShares.toRat =
            (assetsNumber.toRat - NAVShares.toRat / ST) * ST := by field_simp
        calc |assetsNumber.toRat * ST - NAVShares.toRat|
            = |assetsNumber.toRat - NAVShares.toRat / ST| * ST := by
              rw [hrw, abs_mul, abs_of_pos hST_pos]
          _ ≤ NAVShares.toRat / ST * (6 / (2 ^ 63 - 3)) * ST := by
              nlinarith [hST_pos, abs_nonneg (assetsNumber.toRat - NAVShares.toRat / ST), hdivb]
          _ = NAVShares.toRat * (6 / (2 ^ 63 - 3)) := by
              rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hST_pos)]
      -- compose the two stages (exact denominator, `ε₁ = 0`)
      have hcomp := div_pipeline_rel_bound ST ST T0 NAVShares.toRat assetsNumber.toRat
        0 (5 / (2 ^ 63 + 7)) (6 / (2 ^ 63 - 3)) depositε hT0_pos (le_of_lt hANpos)
        (by rw [sub_self, abs_zero, mul_zero]) hmulb h3
        (le_refl 0) (by norm_num) hε₂lt (by norm_num) (by norm_num)
        withdraw_pipeline_up withdraw_pipeline_lo
      -- relative bound on `assetsNumber` about the ideal
      have hAN_bound : |assetsNumber.toRat - T0 / ST| ≤ T0 / ST * depositε := by
        have heq1 : assetsNumber.toRat - T0 / ST = (assetsNumber.toRat * ST - T0) / ST := by
          field_simp
        rw [heq1, abs_div, abs_of_pos hST_pos, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right hcomp (le_of_lt hST_pos)
      obtain ⟨hlo_b, hhi_b⟩ := abs_le.mp hAN_bound
      have hideal_pos : 0 < v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat := by
        rw [hideal_eq, hT0_def]; exact div_pos hT0_pos hST_pos
      -- downward floor
      have hANneg : assetsNumber.negative_ = false := Number.negative_false_of_pos assetsNumber hANpos
      obtain ⟨hfloor_le, hfloor_ulp, hassets_nn⟩ :=
        STAmount.ofNumber_downward_floor_bounds v.numericType assetsNumber assets hANnorm hANneg hof hres_ne
      refine ⟨hassets_nn, le_of_lt hideal_pos, ?_, ?_⟩
      · rw [hideal_eq, hT0_def]
        calc assets.toRat ≤ assetsNumber.toRat := hfloor_le
          _ = T0 / ST + (assetsNumber.toRat - T0 / ST) := by rw [hT0_def]; ring
          _ ≤ T0 / ST + T0 / ST * depositε := by rw [hT0_def] at hhi_b ⊢; linarith [hhi_b]
          _ = nav * shares.toRat / ST * (1 + depositε) := by rw [hT0_def]; ring
      · intro _
        rw [hideal_eq, hT0_def]
        have h1 : T0 / ST - assetsNumber.toRat ≤ T0 / ST * depositε := by
          rw [hT0_def] at hlo_b ⊢; linarith [hlo_b]
        rw [hT0_def] at h1
        linarith [hfloor_ulp, h1]
    · -- zero payout: the shortfall conjunct is vacuous, the others use `assets = 0`
      have haz_true : assets.isZero = true := by
        cases hb : assets.isZero with
        | false => exact absurd hb hzf
        | true => rfl
      have hasset0 : assets.toRat = 0 := by
        have hmv0 : assets.mValue = 0 := by
          have := haz_true; unfold STAmount.isZero at this; exact beq_iff_eq.mp this
        rw [STAmount.toRat_signed, hmv0]; simp
      have hideal_nn : 0 ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat := by
        rw [hideal_eq]
        exact div_nonneg (mul_nonneg hnav_nonneg hnn) (by rw [hST_def]; positivity)
      refine ⟨by rw [hasset0], hideal_nn, ?_, ?_⟩
      · rw [hasset0]; exact mul_nonneg hideal_nn (by linarith)
      · intro hf; rw [haz_true] at hf; exact absurd hf (by decide)

/-- Upper closure of the withdraw `mul`/`div` pipeline within the raw `12/(2^63-3)`. -/
lemma withdraw_pipeline_up12 :
    ((1 : ℚ) + 5 / (2 ^ 63 + 7)) * (1 + 6 / (2 ^ 63 - 3)) ≤ (1 + 12 / (2 ^ 63 - 3)) * (1 - 0) := by
  norm_num

/-- Lower closure of the withdraw `mul`/`div` pipeline within the raw `12/(2^63-3)`. -/
lemma withdraw_pipeline_lo12 :
    ((1 : ℚ) - 12 / (2 ^ 63 - 3)) * (1 + 0) ≤ (1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3)) := by
  norm_num

/-- Composition-grade sibling of `sharesToAssetsWithdraw_spec`: the payout band at
the raw `mul`/`div` pipeline constant `12/(2^63-3)` rather than the widened
`depositε`. The dilution composition needs this tighter granularity; the
`depositε`-level lemma stays as the headline-grade statement. -/
theorem Vault.sharesToAssetsWithdraw_spec_raw (v : Vault)
    (shares assets : STAmount) (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    0 ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat ∧
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + (12 / (2 ^ 63 - 3))) ∧
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (12 / (2 ^ 63 - 3)) +
          (10 : ℚ) ^ assets.exponent) := by
  have hεnn : (0 : ℚ) ≤ (12 / (2 ^ 63 - 3)) := by norm_num
  have hεlt : (12 / (2 ^ 63 - 3)) < 1 := by norm_num
  -- reduce the run and collapse the two subtractions to the exact `nav`
  obtain ⟨nav2, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waiveUnrealizedLoss hok
  have hnav2facts : nav2.isNormalized ∧
      nav2.toRat = (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    obtain ⟨nv, he, heval⟩ := hnav
    cases waiveUnrealizedLoss with
    | false =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm
        v.wf.lossUnrealized_norm hsub, by rw [hval]; exact heval⟩
    | true =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub,
        by rw [hval]; exact heval⟩
  obtain ⟨hnav2norm, hnav2_val⟩ := hnav2facts
  -- `nav` is non-negative on a lawful vault
  have hnav_nonneg : 0 ≤ (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    cases waiveUnrealizedLoss with
    | false =>
      rw [if_neg (by decide)]
      show 0 ≤ v.withdrawNav
      unfold RawVault.withdrawNav; exact v.exact.withdraw_nav_nonneg
    | true =>
      rw [if_pos rfl]
      show 0 ≤ v.depositNav
      unfold RawVault.depositNav
      exact v.exact.assetsTotal_nonneg
  set nav : ℚ := (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) with hnav_def
  rcases hcase with ⟨hnav2m, hzero⟩ |
      ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · -- zero net asset value: the payout is the canonical zero, the ideal is `0`
    subst hzero
    have hnav0 : nav = 0 := by
      have h : nav2.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero nav2 hnav2m
      linarith [hnav2_val]
    have hideal0 : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat = 0 := by
      show nav * shares.toRat / (v.toExact.sharesTotal : ℚ) = 0
      rw [hnav0]; ring
    have haz : (STAmount.zero v.numericType).toRat = 0 := STAmount.zero_toRat v.numericType
    rw [hideal0]
    refine ⟨by rw [haz], le_refl 0, by rw [haz, zero_mul], ?_⟩
    intro hf
    rw [STAmount.zero_isZero] at hf
    exact absurd hf (by decide)
  · -- genuine pricing: run the relative composition, then the downward floor
    set ST : ℚ := (v.toExact.sharesTotal : ℚ) with hST_def
    have hST_eq : ST = v.sharesTotal.toRat := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hideal_eq : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat = nav * shares.toRat / ST := rfl
    obtain ⟨sn0, hsn0ok, hsn0val, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsn_eq : sn0 = sharesNumber := by rw [hsn0ok] at hsn; exact Except.ok.inj hsn
    have hsnnorm : sharesNumber.isNormalized := by rw [← hsn_eq]; exact hsn0norm
    have hsnval : sharesNumber.toRat = shares.toRat := by rw [← hsn_eq]; exact hsn0val
    -- `nav` positive: nonzero pricing forces a nonzero mantissa
    have hnav2_ne0 : nav2.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero nav2 hnav2m
    have hnav_pos : 0 < nav := by
      rcases lt_or_eq_of_le hnav_nonneg with h | h
      · exact h
      · exact absurd (by linarith [hnav2_val] : nav2.toRat = 0) hnav2_ne0
    -- shares total positive
    have hApos : 0 < v.toExact.assetsTotal := by
      have hle : nav ≤ v.toExact.assetsTotal := by
        rw [hnav_def]
        cases waiveUnrealizedLoss with
        | true =>
          rw [if_pos rfl]; show v.depositNav ≤ _; unfold RawVault.depositNav
          linarith
        | false =>
          rw [if_neg (by decide)]; show v.withdrawNav ≤ _; unfold RawVault.withdrawNav
          linarith [v.exact.lossUnrealized_nonneg]
      linarith
    have hST_pos : 0 < ST := by
      rw [hST_def]
      have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
        absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hSTne : v.sharesTotal.toRat ≠ 0 := hST_eq ▸ ne_of_gt hST_pos
    have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero hSTne
    -- decide the output shape
    by_cases hzf : assets.isZero = false
    · -- nonzero payout: full pipeline plus downward floor
      have hres_ne : assets.mValue ≠ 0 := ne_of_beq_false hzf
      have hanm : assetsNumber.mantissa_ ≠ 0 :=
        STAmount.ofNumber_source_ne_zero v.numericType assetsNumber .downward assets hof hres_ne
      have hNAVm : NAVShares.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hdiv hanm
      obtain ⟨hnav2_m', hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
      have hNAVnorm : NAVShares.isNormalized :=
        operator_mul_result_isNormalized nav2 sharesNumber NAVShares .to_nearest
          hnav2norm hsnnorm hnav2m hsn_m hmul hNAVm
      have hshares_pos : 0 < shares.toRat := by
        have hsnne : sharesNumber.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero sharesNumber hsn_m
        rw [hsnval] at hsnne
        exact lt_of_le_of_ne hnn (Ne.symm hsnne)
      set T0 : ℚ := nav * shares.toRat with hT0_def
      have hT0_pos : 0 < T0 := mul_pos hnav_pos hshares_pos
      have hANnorm : assetsNumber.isNormalized :=
        operator_div_result_isNormalized NAVShares v.sharesTotal assetsNumber .to_nearest
          hNAVnorm v.wf.sharesTotal_norm hNAVm hSTm hdiv hanm
      -- stage bounds
      have hmulb : |NAVShares.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
        have hmulraw : |NAVShares.toRat - nav2.toRat * sharesNumber.toRat| ≤
            |nav2.toRat * sharesNumber.toRat| * (5 / (2 ^ 63 + 7)) :=
          operator_mul_rounds_to_nearest nav2 sharesNumber NAVShares hnav2norm hsnnorm hmul hNAVm
        have hval : nav2.toRat * sharesNumber.toRat = T0 := by
          rw [hT0_def, hnav2_val, hsnval]
        rwa [hval, abs_of_pos hT0_pos] at hmulraw
      have hε₂lt : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      have hε₃lt : (6 : ℚ) / (2 ^ 63 - 3) < 1 := by norm_num
      have hNAVpos : 0 < NAVShares.toRat := by
        have := abs_le.mp hmulb; nlinarith [hT0_pos]
      have hAN_ST_pos : 0 < NAVShares.toRat / ST := div_pos hNAVpos hST_pos
      have hdivb : |assetsNumber.toRat - NAVShares.toRat / ST| ≤
          NAVShares.toRat / ST * (6 / (2 ^ 63 - 3)) := by
        have h : |assetsNumber.toRat - NAVShares.toRat / v.sharesTotal.toRat| ≤
            |NAVShares.toRat / v.sharesTotal.toRat| * (6 / (2 ^ 63 - 3)) :=
          operator_div_rounds_to_nearest NAVShares v.sharesTotal assetsNumber
            hNAVnorm v.wf.sharesTotal_norm hdiv hanm
        rw [← hST_eq] at h
        rwa [abs_of_pos hAN_ST_pos] at h
      have hANpos : 0 < assetsNumber.toRat := by
        have := abs_le.mp hdivb; nlinarith [hAN_ST_pos]
      have h3 : |assetsNumber.toRat * ST - NAVShares.toRat| ≤ NAVShares.toRat * (6 / (2 ^ 63 - 3)) := by
        have hrw : assetsNumber.toRat * ST - NAVShares.toRat =
            (assetsNumber.toRat - NAVShares.toRat / ST) * ST := by field_simp
        calc |assetsNumber.toRat * ST - NAVShares.toRat|
            = |assetsNumber.toRat - NAVShares.toRat / ST| * ST := by
              rw [hrw, abs_mul, abs_of_pos hST_pos]
          _ ≤ NAVShares.toRat / ST * (6 / (2 ^ 63 - 3)) * ST := by
              nlinarith [hST_pos, abs_nonneg (assetsNumber.toRat - NAVShares.toRat / ST), hdivb]
          _ = NAVShares.toRat * (6 / (2 ^ 63 - 3)) := by
              rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hST_pos)]
      -- compose the two stages (exact denominator, `ε₁ = 0`)
      have hcomp := div_pipeline_rel_bound ST ST T0 NAVShares.toRat assetsNumber.toRat
        0 (5 / (2 ^ 63 + 7)) (6 / (2 ^ 63 - 3)) (12 / (2 ^ 63 - 3)) hT0_pos (le_of_lt hANpos)
        (by rw [sub_self, abs_zero, mul_zero]) hmulb h3
        (le_refl 0) (by norm_num) hε₂lt (by norm_num) (by norm_num)
        withdraw_pipeline_up12 withdraw_pipeline_lo12
      -- relative bound on `assetsNumber` about the ideal
      have hAN_bound : |assetsNumber.toRat - T0 / ST| ≤ T0 / ST * (12 / (2 ^ 63 - 3)) := by
        have heq1 : assetsNumber.toRat - T0 / ST = (assetsNumber.toRat * ST - T0) / ST := by
          field_simp
        rw [heq1, abs_div, abs_of_pos hST_pos, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right hcomp (le_of_lt hST_pos)
      obtain ⟨hlo_b, hhi_b⟩ := abs_le.mp hAN_bound
      have hideal_pos : 0 < v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat := by
        rw [hideal_eq, hT0_def]; exact div_pos hT0_pos hST_pos
      -- downward floor
      have hANneg : assetsNumber.negative_ = false := Number.negative_false_of_pos assetsNumber hANpos
      obtain ⟨hfloor_le, hfloor_ulp, hassets_nn⟩ :=
        STAmount.ofNumber_downward_floor_bounds v.numericType assetsNumber assets hANnorm hANneg hof hres_ne
      refine ⟨hassets_nn, le_of_lt hideal_pos, ?_, ?_⟩
      · rw [hideal_eq, hT0_def]
        calc assets.toRat ≤ assetsNumber.toRat := hfloor_le
          _ = T0 / ST + (assetsNumber.toRat - T0 / ST) := by rw [hT0_def]; ring
          _ ≤ T0 / ST + T0 / ST * (12 / (2 ^ 63 - 3)) := by rw [hT0_def] at hhi_b ⊢; linarith [hhi_b]
          _ = nav * shares.toRat / ST * (1 + (12 / (2 ^ 63 - 3))) := by rw [hT0_def]; ring
      · intro _
        rw [hideal_eq, hT0_def]
        have h1 : T0 / ST - assetsNumber.toRat ≤ T0 / ST * (12 / (2 ^ 63 - 3)) := by
          rw [hT0_def] at hlo_b ⊢; linarith [hlo_b]
        rw [hT0_def] at h1
        linarith [hfloor_ulp, h1]
    · -- zero payout: the shortfall conjunct is vacuous, the others use `assets = 0`
      have haz_true : assets.isZero = true := by
        cases hb : assets.isZero with
        | false => exact absurd hb hzf
        | true => rfl
      have hasset0 : assets.toRat = 0 := by
        have hmv0 : assets.mValue = 0 := by
          have := haz_true; unfold STAmount.isZero at this; exact beq_iff_eq.mp this
        rw [STAmount.toRat_signed, hmv0]; simp
      have hideal_nn : 0 ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat := by
        rw [hideal_eq]
        exact div_nonneg (mul_nonneg hnav_nonneg hnn) (by rw [hST_def]; positivity)
      refine ⟨by rw [hasset0], hideal_nn, ?_, ?_⟩
      · rw [hasset0]; exact mul_nonneg hideal_nn (by linarith)
      · intro hf; rw [haz_true] at hf; exact absurd hf (by decide)

/-! ## `sharesToAssetsWithdraw_bounds` -/

/-- **Proof body of `Vault.sharesToAssetsWithdraw_bounds`.** Drops the internal
`0 ≤ ideal` conjunct of the spec and widens the ULP term to `2` ULP. -/
theorem Vault.sharesToAssetsWithdraw_bounds_proof (v : Vault)
    (shares assets : STAmount) (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) ∧
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε +
          2 * (10 : ℚ) ^ assets.exponent) := by
  obtain ⟨h1, -, h3, h4⟩ :=
    Vault.sharesToAssetsWithdraw_spec v shares assets waiveUnrealizedLoss hnn hc hnav hok
  refine ⟨h1, h3, fun hz => ?_⟩
  have hpow : (0 : ℚ) ≤ (10 : ℚ) ^ assets.exponent := le_of_lt (zpow_pos (by norm_num) _)
  linarith [h4 hz]

/-! ## `assetsToSharesWithdraw` share specification -/

/-- **Value specification of `assetsToSharesWithdraw`** in the current fixed-assets
withdraw direction (`truncateShares = true`, general `waiveUnrealizedLoss`). The exchange collapses to
the exact pricing net asset value, the `mul`/`div` stages round within `depositε`, and
the round-to-nearest `ofNumber .int64` lands within half a share: the returned amount is
a positive integer sitting within `depositε` relatively plus half a share of
`idealSharesWithdraw`. The withdraw analog of `assetsToSharesWithdraw_spec`. -/
lemma Vault.assetsToSharesWithdraw_within (v : Vault) (assets shares : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hpos : 0 < assets.toRat) (hc : assets.Canonical)
    (hok : assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok shares)
    (hnz : shares.isZero = false) :
    0 < v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat ∧
    shares.toRat.den = 1 ∧ 0 < shares.toRat ∧
    |shares.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat|
      ≤ v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * depositε + 1 := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false (show (shares.mValue == 0) = false from hnz)
  obtain ⟨nav2, hsub, hcase⟩ :=
    assetsToSharesWithdraw_ok_reduces v assets shares true waiveUnrealizedLoss hok
  have hnav2facts : nav2.isNormalized ∧
      nav2.toRat = (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    obtain ⟨nv, he, heval⟩ := hnav
    cases waiveUnrealizedLoss with
    | false =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm
        v.wf.lossUnrealized_norm hsub, by rw [hval]; exact heval⟩
    | true =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub,
        by rw [hval]; exact heval⟩
  have hnav_nonneg : 0 ≤ (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    cases waiveUnrealizedLoss with
    | false =>
      rw [if_neg (by decide)]; show 0 ≤ v.withdrawNav
      unfold RawVault.withdrawNav; exact v.exact.withdraw_nav_nonneg
    | true =>
      rw [if_pos rfl]; show 0 ≤ v.depositNav
      unfold RawVault.depositNav
      exact v.exact.assetsTotal_nonneg
  set navval : ℚ := (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) with hnavval_def
  obtain ⟨hnav2norm, hnav2val⟩ := hnav2facts
  rcases hcase with ⟨hzm, hzero⟩ | ⟨hnz2, assetsNumber, sharesAssets, sharesNumber, sharesNumber',
      han, hmul, hdiv, htrunc, hofn⟩
  · exfalso; rw [hzero, STAmount.zero_mValue] at hmv; exact hmv rfl
  -- nav2 positive
  have hnav2_pos : 0 < nav2.toRat := by
    have hne : nav2.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero nav2 hnz2
    rw [hnav2val] at hne ⊢; exact lt_of_le_of_ne hnav_nonneg (Ne.symm hne)
  -- shares total positive integer
  have hS_pos : 0 < v.sharesTotal.toRat := by
    rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
    · exact h
    · exfalso
      have hz : v.toExact.sharesTotal = 0 := by
        show v.sharesTotal.toRat.num.toNat = 0; rw [← h]; rfl
      obtain ⟨hAT, -⟩ := v.exact.empty_shares hz
      have hle0 : navval ≤ 0 := by
        rw [hnavval_def]
        cases waiveUnrealizedLoss with
        | false =>
          rw [if_neg (by decide)]; unfold RawVault.withdrawNav; rw [hAT]
          linarith [v.exact.lossUnrealized_nonneg]
        | true =>
          rw [if_pos rfl]; unfold RawVault.depositNav; rw [hAT]
      rw [hnav2val] at hnav2_pos; linarith
  have hS_one : 1 ≤ v.sharesTotal.toRat := by
    have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hS_pos
    have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
      rw [v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hS_pos.ne'
  -- assets lift
  obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact assets .to_nearest hc
  have haneq : an' = assetsNumber := by rw [han'] at han; exact Except.ok.inj han
  rw [haneq] at hanval hannorm
  have hApos : 0 < assetsNumber.toRat := by rw [hanval]; exact hpos
  have hAm : assetsNumber.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hApos.ne'
  have hmv_assets : assets.mValue ≠ 0 := by
    intro h0; apply hpos.ne'; rw [STAmount.toRat_signed, h0]; simp
  have hfloor : (10 : ℚ) ^ (-81 : ℤ) ≤ |assets.toRat| :=
    STAmount.Canonical.abs_toRat_ge assets hc hmv_assets
  -- The current fixed-assets path truncates the pre-conversion share Number.
  -- A nonzero packed result therefore witnesses a nonzero truncation source.
  have hQm : sharesNumber.mantissa_ ≠ 0 := by
    have hsn' : sharesNumber'.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 sharesNumber' .to_nearest shares
        (by decide) hofn hmv
    exact Number.truncate_source_ne_zero sharesNumber sharesNumber' htrunc hsn'
  -- the product is nonzero: the true value clears the underflow floor
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
      = v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat := by
    unfold RawVault.idealSharesWithdraw
    rw [hanval, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, hnav2val, ← hnavval_def]
  have hideal_pos : 0 < v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat := by
    rw [← hideal_eq]; exact div_pos (mul_pos hS_pos hApos) hnav2_pos
  rw [hideal_eq] at hQbound
  -- The current path truncates toward the floor, so the final packing is within
  -- one whole share (not the obsolete nearest half-share bound).
  have hsnneg : sharesNumber.negative_ = false := Number.negative_false_of_pos sharesNumber hQpos
  have htr : sharesNumber.truncate = .ok sharesNumber' := htrunc
  obtain ⟨htrval, htrnorm⟩ := Number.truncate_floor sharesNumber sharesNumber' hQnorm hsnneg htr
  have hsn'm : sharesNumber'.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 sharesNumber' .to_nearest shares
      (by decide) hofn hmv
  have hshval : shares.toRat = sharesNumber'.toRat :=
    STAmount.ofNumber_integral_exact .int64 sharesNumber' .to_nearest shares (by decide)
      (htrnorm hsn'm) (by rw [htrval]; exact Rat.den_intCast _) hofn
  have hden : shares.toRat.den = 1 := by rw [hshval, htrval]; exact Rat.den_intCast _
  have hnn_sh : 0 ≤ shares.toRat := by
    rw [hshval, htrval]
    exact_mod_cast Int.floor_nonneg.mpr (le_of_lt hQpos)
  have hwithin : |shares.toRat - sharesNumber.toRat| ≤ 1 := by
    rw [hshval, htrval]
    have hfloor_le : (Int.floor sharesNumber.toRat : ℚ) ≤ sharesNumber.toRat := by exact_mod_cast Int.floor_le _
    have hfloor_lt' : sharesNumber.toRat < ((Int.floor sharesNumber.toRat + 1 : ℤ) : ℚ) := by
      exact_mod_cast (Int.lt_floor_add_one sharesNumber.toRat)
    have hcast : ((Int.floor sharesNumber.toRat + 1 : ℤ) : ℚ) =
        (Int.floor sharesNumber.toRat : ℚ) + 1 := by norm_num
    rw [hcast] at hfloor_lt'
    rw [abs_of_nonpos (by linarith [hfloor_le])]
    linarith [hfloor_lt']
  -- a nonzero int64 output is strictly positive
  have hshc : shares.IntegralCanonical :=
    (assetsToSharesWithdraw_int64_canonical v assets shares true waiveUnrealizedLoss hok hnz).1
  have hsh_pos : 0 < shares.toRat := by
    have hsh_floor : (10 : ℚ) ^ (-81 : ℤ) ≤ |shares.toRat| :=
      STAmount.canonical_disj_abs_toRat_ge shares (Or.inr hshc) hmv
    have hne : shares.toRat ≠ 0 := by
      intro h; rw [h, abs_zero] at hsh_floor; exact absurd hsh_floor (by norm_num)
    exact lt_of_le_of_ne hnn_sh (Ne.symm hne)
  refine ⟨hideal_pos, hden, hsh_pos, ?_⟩
  calc |shares.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat|
      ≤ |shares.toRat - sharesNumber.toRat|
        + |sharesNumber.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat| :=
        abs_sub_le _ _ _
    _ ≤ v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * depositε + 1 := by
        linarith [hwithin, hQbound]

/-- **Proof body of `Vault.withdraw_sharesBurned`.** The named asset amount prices
through `assetsToSharesWithdraw` into the burned shares. -/
theorem Vault.withdraw_sharesBurned_proof (v : Vault) (assets : STAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < assets.toRat) (hc : assets.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned.toRat.den = 1 ∧ 0 < r.sharesBurned.toRat ∧
    |r.sharesBurned.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat| ≤
      1 + v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * depositε := by
  obtain ⟨cw, an, sta, hcomp, herr2, -, -, -, hsb, -⟩ :=
    Vault.withdraw_success_reduces v (.vaultAssets assets) waiveUnrealizedLoss r hok herr
  obtain ⟨shares, hshares, hsnz, -, hsr⟩ :=
    computeWithdrawByAssets_none_reduces v assets waiveUnrealizedLoss cw hcomp herr2
  have hrsb : r.sharesBurned = shares := by rw [hsb, hsr]
  obtain ⟨-, hden, hsh_pos, hbound⟩ :=
    Vault.assetsToSharesWithdraw_within v assets shares waiveUnrealizedLoss hnav hpos hc
      hshares hsnz
  rw [hrsb]
  exact ⟨hden, hsh_pos, by linarith [hbound]⟩

/-! ## `Vault.withdraw` payout bound -/

/-- **Raw pricing and final-debit provenance of a non-final withdrawal.** The
exchange result is used only for pricing and the availability guard. The source
then clamps its negation, accepts precision, and debits that final amount. -/
lemma Vault.withdraw_payout_priced (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ (cw : ComputeWithdrawResult) (rawAssetsNumber sharesBurnedNumber assetDebitedNumber
        assetsTotal' assetsAvailable' sharesTotal' : Number),
      (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss) = .ok cw ∧
      cw.error = none ∧
      cw.assets'.toNumber .to_nearest = .ok rawAssetsNumber ∧
      v.assetsAvailable.operator_lt rawAssetsNumber = false ∧
      r.sharesBurned = cw.sharesRedeemed ∧
      v.sharesToAssetsWithdraw cw.sharesRedeemed waiveUnrealizedLoss = .ok cw.assets' ∧
      clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok r.assets' ∧
      r.assets'.isFractionalNonPositive = .ok false ∧
      r.assets'.toNumber .to_nearest = .ok assetDebitedNumber ∧
      cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber ∧
      v.assetsTotal.operator_sub assetDebitedNumber .to_nearest = .ok assetsTotal' ∧
      v.assetsAvailable.operator_sub assetDebitedNumber .to_nearest = .ok assetsAvailable' ∧
      v.sharesTotal.operator_sub sharesBurnedNumber .to_nearest = .ok sharesTotal' := by
  obtain ⟨cw, rawN, sta, hcomp, herr2, hraw, havail, hsta, hsb, hdisj⟩ :=
    Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr
  have hsta_eq : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  have hprice : v.sharesToAssetsWithdraw cw.sharesRedeemed waiveUnrealizedLoss = .ok cw.assets' := by
    cases amount with
    | vaultAssets a =>
      obtain ⟨sh, -, -, hs, hsr⟩ :=
        computeWithdrawByAssets_none_reduces v a waiveUnrealizedLoss cw hcomp herr2
      rw [hsr]; exact hs
    | vaultShares sh =>
      obtain ⟨hs, hsr⟩ := computeWithdrawByShares_none_reduces v sh waiveUnrealizedLoss cw hcomp herr2
      rw [hsr]; exact hs
  rcases hdisj with ⟨hfinal, -⟩ |
      ⟨hfinal, sbn, debitN, at', av', st', debit, atr, atr', hsbn, hclamp, hprecision,
        hdebit, hat, hatr, hatr', hguard, hav, hst', hrassets, hrv⟩
  · exfalso
    rw [hsta_eq, ← hsb] at hfinal
    rw [hfinal] at hfin
    exact absurd hfin (by simp)
  · refine ⟨cw, rawN, sbn, debitN, at', av', st', hcomp, herr2, hraw, havail, hsb, hprice,
      ?_, ?_, ?_, hsbn, hat, hav, hst'⟩
    · rw [hrassets]; exact hclamp
    · rw [hrassets]; exact hprecision
    · rw [hrassets]; exact hdebit

/-- **Proof body of `Vault.withdraw_payout`.** Reprices the burned shares through
`sharesToAssetsWithdraw_spec`. -/
theorem Vault.withdraw_payout_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ rawPayout : STAmount,
      v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok rawPayout ∧
      clampToSumExponent v.assetsTotal rawPayout.operator_neg = .ok r.assets' ∧
      r.assets'.isFractionalNonPositive = .ok false ∧
      ∃ debitNumber assetsTotal' assetsAvailable' : Number,
        r.assets'.toNumber .to_nearest = .ok debitNumber ∧
        v.assetsTotal.operator_sub debitNumber .to_nearest = .ok assetsTotal' ∧
        v.assetsAvailable.operator_sub debitNumber .to_nearest = .ok assetsAvailable' ∧
        0 ≤ rawPayout.toRat ∧
        rawPayout.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) ∧
        (rawPayout.isZero = false →
          v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
            v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
              2 * (10 : ℚ) ^ rawPayout.exponent + |r.assets'.toRat - rawPayout.toRat|) := by
  obtain ⟨cw, rawN, sbn, debitN, at', av', st', hcomp, herr2, hrawN, havail, hsb,
    hraw, hclamp, hprecision, hdebit, hsbn, hat, hav, hst'⟩ :=
    Vault.withdraw_payout_priced v amount waiveUnrealizedLoss sharesTotalAmount r hok herr hst hfin
  have hprice : v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok cw.assets' := by
    rw [hsb]; exact hraw
  obtain ⟨hraw_nn, hraw_hi, hraw_lo⟩ :=
    Vault.sharesToAssetsWithdraw_bounds_proof v r.sharesBurned cw.assets' waiveUnrealizedLoss
      hnn hc hnav hprice
  refine ⟨cw.assets', hprice, ?_, ?_, debitN, at', av', hdebit, hat, hav, hraw_nn, hraw_hi, ?_⟩
  · exact hclamp
  · exact hprecision
  · intro hraw_nz
    have h := hraw_lo hraw_nz
    have habs : cw.assets'.toRat - r.assets'.toRat ≤ |r.assets'.toRat - cw.assets'.toRat| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith

/-! ## `withdraw_payout_integral` -/

/-- **Waive-general recovery-pipeline bound.** The general-`waiveUnrealizedLoss`
companion of the shared `false`-only `recovery_pipeline_bound`: the payout is
`ofNumber rv.numericType aN .downward`, and the exact `sharesToAssetsWithdraw`
ideal sits within `depositε` of `aN` when `aN` is nonzero, or is `Number`-underflow
tiny when `aN` is zero. -/
lemma Vault.recovery_pipeline_bound_gen (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss) (hc : shares.Canonical)
    (hnav_pos : 0 < (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav))
    (hshpos : 0 < shares.toRat)
    (hprice : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    ∃ aN : Number,
      STAmount.ofNumber v.numericType aN .downward = .ok assets ∧
      (aN.mantissa_ ≠ 0 → aN.isNormalized ∧ aN.negative_ = false ∧
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat ≤
          aN.toRat + v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε) ∧
      (aN.mantissa_ = 0 →
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat ≤ (10 : ℚ) ^ (-32700 : ℤ)) := by
  obtain ⟨nav2, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waiveUnrealizedLoss hprice
  have hnav2facts : nav2.isNormalized ∧
      nav2.toRat = (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    obtain ⟨nv, he, heval⟩ := hnav
    cases waiveUnrealizedLoss with
    | false =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm
        v.wf.lossUnrealized_norm hsub, by rw [hval]; exact heval⟩
    | true =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub,
        by rw [hval]; exact heval⟩
  set navval : ℚ := (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) with hnavval_def
  obtain ⟨hnav2norm, hnav2val⟩ := hnav2facts
  have hnav2_pos : 0 < nav2.toRat := by rw [hnav2val]; exact hnav_pos
  have hST_pos : 0 < v.sharesTotal.toRat := by
    rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
    · exact h
    · exfalso
      have hz : v.toExact.sharesTotal = 0 := by
        show v.sharesTotal.toRat.num.toNat = 0; rw [← h]; rfl
      obtain ⟨hAT, -⟩ := v.exact.empty_shares hz
      have hle0 : navval ≤ 0 := by
        rw [hnavval_def]
        cases waiveUnrealizedLoss with
        | false =>
          rw [if_neg (by decide)]; unfold RawVault.withdrawNav; rw [hAT]
          linarith [v.exact.lossUnrealized_nonneg]
        | true =>
          rw [if_pos rfl]; unfold RawVault.depositNav; rw [hAT]
      rw [hnav2val] at hnav2_pos; linarith
  have hST_one : 1 ≤ v.sharesTotal.toRat := by
    have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hST_pos
    have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
      rw [v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hST_pos.ne'
  set ideal : ℚ := v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat with hideal_def
  have hideal_eq : ideal = nav2.toRat * shares.toRat / v.sharesTotal.toRat := by
    rw [hideal_def]; unfold RawVault.idealAssetsWithdraw
    rw [hnav2val, ← hnavval_def, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  rcases hcase with ⟨hnav2m0, hzero⟩ |
      ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · exfalso
    have : nav2.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero nav2 hnav2m0
    linarith [hnav2_pos]
  · obtain ⟨sn0, hsn0ok, hsn0val, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsn_eq : sharesNumber = sn0 := Except.ok.inj (hsn.symm.trans hsn0ok)
    have hsnnorm : sharesNumber.isNormalized := by rw [hsn_eq]; exact hsn0norm
    have hsnval : sharesNumber.toRat = shares.toRat := by rw [hsn_eq]; exact hsn0val
    have hsn_pos : 0 < sharesNumber.toRat := by rw [hsnval]; exact hshpos
    have hideal_eq' : ideal = nav2.toRat * sharesNumber.toRat / v.sharesTotal.toRat := by
      rw [hideal_eq, hsnval]
    refine ⟨assetsNumber, hof, ?_, ?_⟩
    · intro hQm
      have hNAVm : NAVShares.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hdiv hQm
      obtain ⟨hnav2_m', hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
      obtain ⟨hQnorm, hQpos, hQbound⟩ :=
        RawVault.exchange_pipeline_within nav2 sharesNumber v.sharesTotal NAVShares assetsNumber
          hnav2norm hsnnorm v.wf.sharesTotal_norm hnav2_pos hsn_pos hST_pos hmul hdiv hNAVm hQm
      rw [← hideal_eq'] at hQbound
      have hANneg : assetsNumber.negative_ = false := Number.negative_false_of_pos assetsNumber hQpos
      obtain ⟨_, hhi⟩ := abs_le.mp hQbound
      exact ⟨hQnorm, hANneg, by linarith [hhi]⟩
    · intro hQm0
      have hunit : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) = (10 : ℚ) ^ (-32750 : ℤ) := by
        rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        norm_num [minExponent]
      have hu_pos : (0 : ℚ) < (10 : ℚ) ^ (-32750 : ℤ) := zpow_pos (by norm_num) _
      have h2u_le : 2 * (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-32700 : ℤ) := by
        rw [show (10 : ℚ) ^ (-32700 : ℤ) = (10 : ℚ) ^ (50 : ℤ) * (10 : ℚ) ^ (-32750 : ℤ) from by
          rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num]
        have h50 : (2 : ℚ) ≤ (10 : ℚ) ^ (50 : ℤ) := by norm_num
        nlinarith [hu_pos, h50]
      have hbound : ideal < 2 * (10 : ℚ) ^ (-32750 : ℤ) := by
        by_cases hPm0 : NAVShares.mantissa_ = 0
        · have hsmall := operator_mul_underflow_truth_small nav2 sharesNumber NAVShares .to_nearest
            hnav2norm hsnnorm (Number.mantissa_ne_zero_of_toRat_ne_zero hnav2_pos.ne')
            (Number.mantissa_ne_zero_of_toRat_ne_zero hsn_pos.ne') hmul hPm0
          have hprod_pos : 0 < nav2.toRat * sharesNumber.toRat := mul_pos hnav2_pos hsn_pos
          rw [abs_of_pos hprod_pos, hunit] at hsmall
          have hle : ideal ≤ nav2.toRat * sharesNumber.toRat := by
            rw [hideal_eq']
            calc nav2.toRat * sharesNumber.toRat / v.sharesTotal.toRat
                ≤ nav2.toRat * sharesNumber.toRat / 1 :=
                  div_le_div_of_nonneg_left (le_of_lt hprod_pos) (by norm_num) hST_one
              _ = nav2.toRat * sharesNumber.toRat := by ring
          nlinarith [hsmall, hle, hu_pos]
        · have hNAVnorm : NAVShares.isNormalized :=
            operator_mul_result_isNormalized nav2 sharesNumber NAVShares .to_nearest
              hnav2norm hsnnorm (Number.mantissa_ne_zero_of_toRat_ne_zero hnav2_pos.ne')
              (Number.mantissa_ne_zero_of_toRat_ne_zero hsn_pos.ne') hmul hPm0
          have hsmall := operator_div_underflow_truth_small NAVShares v.sharesTotal assetsNumber
            .to_nearest hNAVnorm v.wf.sharesTotal_norm hPm0 hSTm hdiv hQm0
          have hmulbound : |NAVShares.toRat - nav2.toRat * sharesNumber.toRat|
              ≤ |nav2.toRat * sharesNumber.toRat| * (5 / (2 ^ 63 + 7)) :=
            operator_mul_rounds_to_nearest nav2 sharesNumber NAVShares hnav2norm hsnnorm hmul hPm0
          have hprodpos : 0 < nav2.toRat * sharesNumber.toRat := mul_pos hnav2_pos hsn_pos
          rw [abs_of_pos hprodpos] at hmulbound
          have hNAVpos : 0 < NAVShares.toRat := by
            have := abs_le.mp hmulbound; nlinarith [hprodpos]
          have hNAV_close : nav2.toRat * sharesNumber.toRat ≤ NAVShares.toRat * 2 := by
            have := abs_le.mp hmulbound; nlinarith [hprodpos]
          rw [abs_of_nonneg (le_of_lt (div_pos hNAVpos hST_pos)), hunit] at hsmall
          have hle : ideal ≤ NAVShares.toRat / v.sharesTotal.toRat * 2 := by
            rw [hideal_eq', div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right hNAV_close (le_of_lt hST_pos)
          nlinarith [hsmall, hle, div_pos hNAVpos hST_pos]
      linarith [hbound, h2u_le]

/-- **Proof body of `Vault.withdraw_payout_integral`.** The integral floor is within
one whole unit (`10 ^ 0 = 1`): a nonzero payout uses the one-ULP spec conjunct at
exponent `0`, a zero payout uses `recovery_pipeline_bound_gen` and the integral
zero-floor (`aN < 1`). -/
theorem Vault.withdraw_payout_integral_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ rawPayout : STAmount,
      v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok rawPayout ∧
      clampToSumExponent v.assetsTotal rawPayout.operator_neg = .ok r.assets' ∧
      r.assets'.isFractionalNonPositive = .ok false := by
  obtain ⟨raw, hraw, hclamp, hprecision, -⟩ :=
    Vault.withdraw_payout_proof v amount waiveUnrealizedLoss sharesTotalAmount r
      hnn hc hnav hok herr hst hfin
  exact ⟨raw, hraw, hclamp, hprecision⟩

/-! ## `withdraw_vault_updates` support -/

/-- A normalized non-negative `Number` has a clear sign bit. Local copy (the
`ClawbackAccuracy` original imports this file). -/
private lemma wb_neg_false_of_norm_nonneg (n : Number) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) : n.negative_ = false := by
  rcases hb : n.negative_ with _ | _
  · rfl
  · exfalso
    have hle := Number.toRat_nonpos_of_negative n hb
    have hm0 : n.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp (le_antisymm hle h0)
    exact Number.mantissa_ne_zero_of_negative n hn hb hm0

/-- A normalized `Number` whose magnitude clears `10⁻⁸¹` has exponent `≥ -99`. Local
copy (the `ClawbackAccuracy` original imports this file). -/
private lemma wb_exp_ge_of_abs (n : Number) (hn : n.isNormalized)
    (hne : n.mantissa_ ≠ 0) (h : (10 : ℚ) ^ (-81 : ℤ) ≤ |n.toRat|) :
    (-99 : ℤ) ≤ n.exponent_ := by
  obtain ⟨-, hhi⟩ := hn.mantissaBounds_nat hne
  have hmlt : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hhi
  have hpe_pos : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
  have hstep : (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_
      < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ :=
    mul_lt_mul_of_pos_right hmlt hpe_pos
  have hcombine : (10 : ℚ) ^ (-81 : ℤ) < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ := by
    have heq : |n.toRat| = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ := abs_toRat_eq n
    rw [heq] at h; linarith [hstep]
  rw [← zpow_natCast (10 : ℚ) 19, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)] at hcombine
  have hlt : (-81 : ℤ) < ((19 : ℕ) : ℤ) + n.exponent_ :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp hcombine
  omega

/-- A den-`1` rational equals its integer numerator, cast back to `ℚ`. Local copy. -/
private lemma wb_eq_intCast_of_den_one {q : ℚ} (h : q.den = 1) : q = (q.num : ℚ) := by
  conv_lhs => rw [← Rat.num_div_den q]
  rw [h]; simp

/-- **`navSlack` budget of the pricing subtraction.** On a lawful vault, the
computed net asset value `nav2` (`assetsTotal - lossUnrealized`, or `assetsTotal`
with the loss waived) sits within `depositε · assetsTotal` of the exact pricing
value. The single subtraction is correctly rounded within `6 / (2⁶³ - 3)` relative to
its operands (about `15×` under `depositε`), and the flush-to-zero degeneracy is ruled
out by lawfulness: an underflow to zero forces `lossUnrealized = 0` with a zero
`assetsTotal`, contradicting the nonzero-`nav2` branch. This is the `navSlack` half of
`sharesToAssetsWithdraw_total`; `rv.navSlack = depositε · (assetsTotal + assetsTotal)`
dominates `depositε · assetsTotal` since `assetsTotal ≥ 0`. -/
lemma Vault.withdraw_nav_within (v : Vault) (waiveUnrealizedLoss : Bool)
    (nav2 : Number)
    (hsub : v.assetsTotal.operator_sub
        (match waiveUnrealizedLoss with | true => Number.zero | false => v.lossUnrealized)
        .to_nearest = .ok nav2)
    (hgen : nav2.mantissa_ ≠ 0) :
    |nav2.toRat - (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav)|
      ≤ depositε * v.assetsTotal.toRat := by
  set a := v.assetsTotal.toRat with ha_def
  set l := v.lossUnrealized.toRat with hl_def
  have ha_nn : 0 ≤ a := v.exact.assetsTotal_nonneg
  have hl_nn : 0 ≤ l := v.exact.lossUnrealized_nonneg
  have hwd_nn : 0 ≤ a - l := v.exact.withdraw_nav_nonneg
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hε'le : (6 / (2 ^ 63 - 3 : ℚ)) ≤ depositε := by rw [depositε_eq]; norm_num
  cases waiveUnrealizedLoss with
  | true =>
    rw [if_pos rfl]
    have hz : nav2 = v.assetsTotal :=
      Number.operator_sub_zero_right v.assetsTotal Number.zero nav2 rfl hsub
    have hnav2a : nav2.toRat = a := by rw [hz, ha_def]
    have hdep : v.depositNav = a := by rw [ha_def]; rfl
    rw [hnav2a, hdep, sub_self, abs_zero]
    exact mul_nonneg hεnn ha_nn
  | false =>
    rw [if_neg (by decide)]
    have hwith : v.withdrawNav = a - l := by rw [ha_def, hl_def]; rfl
    rw [hwith]
    by_cases hlm : v.lossUnrealized.mantissa_ = 0
    · have hz : nav2 = v.assetsTotal :=
        Number.operator_sub_zero_right v.assetsTotal v.lossUnrealized nav2 hlm hsub
      have hl0 : l = 0 := by rw [hl_def]; exact Number.toRat_eq_zero_of_mantissa_zero v.lossUnrealized hlm
      have hnav2a : nav2.toRat = a := by rw [hz, ha_def]
      rw [hnav2a, hl0, sub_zero, sub_self, abs_zero]
      exact mul_nonneg hεnn ha_nn
    · have hlne : l ≠ 0 := by
        rw [hl_def]; exact Number.toRat_ne_zero_of_mantissa_ne_zero v.lossUnrealized hlm
      have ham : v.assetsTotal.mantissa_ ≠ 0 := by
        intro ha0
        have haz : a = 0 := by rw [ha_def]; exact Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal ha0
        have : 0 < l := lt_of_le_of_ne hl_nn (Ne.symm hlne)
        linarith
      have hne : ¬ v.assetsTotal.operator_eq v.lossUnrealized = true := by
        intro heq
        have : nav2 = Number.zero :=
          Number.operator_sub_eq_zero_of_operator_eq v.assetsTotal v.lossUnrealized nav2
            ham hlm heq hsub
        rw [this] at hgen; exact hgen rfl
      have hr := operator_sub_rounds_to_nearest v.assetsTotal v.lossUnrealized nav2
        v.wf.assetsTotal_norm v.wf.lossUnrealized_norm ham hlm hne hsub hgen
      have hr' : |nav2.toRat - (a - l)| ≤ |a - l| * (6 / (2 ^ 63 - 3 : ℚ)) := hr
      rw [abs_of_nonneg hwd_nn] at hr'
      calc |nav2.toRat - (a - l)| ≤ (a - l) * (6 / (2 ^ 63 - 3 : ℚ)) := hr'
        _ ≤ (a - l) * depositε := mul_le_mul_of_nonneg_left hε'le hwd_nn
        _ ≤ a * depositε := mul_le_mul_of_nonneg_right (by linarith) hεnn
        _ = depositε * a := by ring

/-! ## Weak monotonicity of the `to_nearest` subtraction -/

/-- **Upper monotonicity of `operator_sub` under `.to_nearest`.** When the exact
difference `x - y` is at most a representable `z`, so is the rounded result: no
representable lies strictly between the truth and a value above `z`. -/
lemma Number.operator_sub_to_nearest_le (x y z result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hne : ¬ x.operator_eq y)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hres : result.mantissa_ ≠ 0)
    (hz_ge : x.toRat - y.toRat ≤ z.toRat) :
    result.toRat ≤ z.toRat := by
  by_contra hlt
  push_neg at hlt
  have hyneg_norm : (y.operator_neg).isNormalized := Number.operator_neg_isNormalized y hy
  have hyneg_m : (y.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne y hym]; exact hym
  have hnz : ¬ x.operator_eq ((y.operator_neg).operator_neg) := by
    rw [neg_neg_of_mant_ne hym]; exact hne
  have hok' : Number.operator_add x (y.operator_neg) .to_nearest = .ok result := hok
  have hyneg_val : (y.operator_neg).toRat = - y.toRat := Number.toRat_neg y
  have h_ge : x.toRat + (y.operator_neg).toRat ≤ result.toRat := by
    rw [hyneg_val]; linarith [hz_ge, hlt]
  have hcontra := operator_add_no_inbetween_above x (y.operator_neg) result hx hyneg_norm
    hxm hyneg_m hnz hok' hres h_ge
  exact hcontra z hz hlt (by rw [hyneg_val]; linarith [hz_ge])

/-- **Lower monotonicity of `operator_sub` under `.to_nearest`.** When a representable
`z` is at most the exact difference `x - y`, it is at most the rounded result. -/
lemma Number.operator_sub_to_nearest_ge (x y z result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hne : ¬ x.operator_eq y)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hres : result.mantissa_ ≠ 0)
    (hz_le : z.toRat ≤ x.toRat - y.toRat) :
    z.toRat ≤ result.toRat := by
  by_contra hlt
  push_neg at hlt
  have hyneg_norm : (y.operator_neg).isNormalized := Number.operator_neg_isNormalized y hy
  have hyneg_m : (y.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne y hym]; exact hym
  have hnz : ¬ x.operator_eq ((y.operator_neg).operator_neg) := by
    rw [neg_neg_of_mant_ne hym]; exact hne
  have hok' : Number.operator_add x (y.operator_neg) .to_nearest = .ok result := hok
  have hyneg_val : (y.operator_neg).toRat = - y.toRat := Number.toRat_neg y
  have h_le : result.toRat ≤ x.toRat + (y.operator_neg).toRat := by
    rw [hyneg_val]; linarith [hz_le, hlt]
  have hcontra := operator_add_no_inbetween_below_to_nearest x (y.operator_neg) result hx hyneg_norm
    hxm hyneg_m hnz hok' hres h_le
  exact hcontra z hz hlt (by rw [hyneg_val]; linarith [hz_le])

/-- **Subtracting a non-negative operand under `.to_nearest` never overshoots the
minuend.** The rounded difference `x - y` is at most `x`: a zero result is `≤ x`
because `x ≥ 0`, an equal-operand cancellation gives the zero result, and the
generic case is `operator_sub_to_nearest_le` at `z = x` (using `x - y ≤ x`). -/
lemma Number.operator_sub_nonneg_le (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : x.operator_sub y .to_nearest = .ok result) :
    result.toRat ≤ x.toRat := by
  by_cases hresm : result.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero result hresm]; exact hxnn
  · have hne : ¬ x.operator_eq y := fun heq => by
      have hres0 := Number.operator_sub_eq_zero_of_operator_eq x y result hxm hym heq hok
      rw [hres0] at hresm; exact hresm rfl
    exact Number.operator_sub_to_nearest_le x y x result hx hy hx hxm hym hne hok hresm
      (by linarith [hynn])

lemma Vault.withdraw_nav2_nonneg (v : Vault) (waiveUnrealizedLoss : Bool)
    (nav2 : Number)
    (hsub : v.assetsTotal.operator_sub
        (match waiveUnrealizedLoss with | true => Number.zero | false => v.lossUnrealized)
        .to_nearest = .ok nav2) :
    0 ≤ nav2.toRat := by
  set nl := (match waiveUnrealizedLoss with | true => Number.zero | false => v.lossUnrealized) with hnl_def
  have hnl_norm : nl.isNormalized := by
    cases waiveUnrealizedLoss with
    | true => exact Or.inl rfl
    | false => exact v.wf.lossUnrealized_norm
  have hnl_nn : 0 ≤ nl.toRat := by
    cases waiveUnrealizedLoss with
    | true => rw [show nl = Number.zero from rfl, Number.toRat_zero]
    | false => exact v.exact.lossUnrealized_nonneg
  have hsub_nn : 0 ≤ v.assetsTotal.toRat - nl.toRat := by
    cases waiveUnrealizedLoss with
    | true => rw [show nl = Number.zero from rfl, Number.toRat_zero, sub_zero]; exact v.exact.assetsTotal_nonneg
    | false => rw [show nl = v.lossUnrealized from rfl]; exact v.exact.withdraw_nav_nonneg
  by_cases hn2m : nav2.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero nav2 hn2m]
  · by_cases hnlm : nl.mantissa_ = 0
    · have hz : nav2 = v.assetsTotal := Number.operator_sub_zero_right v.assetsTotal nl nav2 hnlm hsub
      rw [hz]; exact v.exact.assetsTotal_nonneg
    · have ham : v.assetsTotal.mantissa_ ≠ 0 := by
        intro ha0
        have haz : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal ha0
        exact hnlm (Number.toRat_eq_zero_iff.mp (by linarith))
      by_cases heq : v.assetsTotal.operator_eq nl = true
      · have hz0 : nav2 = Number.zero :=
          Number.operator_sub_eq_zero_of_operator_eq v.assetsTotal nl nav2 ham hnlm heq hsub
        rw [hz0, Number.toRat_zero]
      · have := Number.operator_sub_to_nearest_ge v.assetsTotal nl Number.zero nav2
          v.wf.assetsTotal_norm hnl_norm (Or.inl rfl) ham hnlm heq hsub hn2m
          (by rw [Number.toRat_zero]; linarith)
        rwa [Number.toRat_zero] at this


/-- **Proof body of `Vault.sharesToAssetsWithdraw_total`.** Drops the exact-pricing
hypothesis: the two subtractions computing the net asset value round, and the
`navSlack` term absorbs that pricing error. The pipeline runs against the
actually computed `nav2`, which sits within `depositε · assetsTotal ≤ navSlack`
of the exact pricing and stays nonnegative on a lawful vault. -/

theorem Vault.sharesToAssetsWithdraw_total_proof (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    assets.toRat ≤
      (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ)) * (1 + depositε) ∧
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ) * (1 + depositε) +
          2 * (10 : ℚ) ^ assets.exponent) := by
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hεlt : depositε < 1 := by rw [depositε_eq]; norm_num
  obtain ⟨nav2, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waiveUnrealizedLoss hok
  -- exact-pricing net asset value facts
  set a := v.assetsTotal.toRat with ha_def
  set l := v.lossUnrealized.toRat with hl_def
  have ha_nn : 0 ≤ a := v.exact.assetsTotal_nonneg
  have hl_nn : 0 ≤ l := v.exact.lossUnrealized_nonneg
  set nav : ℚ := (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) with hnav_def
  have hnav_nonneg : 0 ≤ nav := by
    rw [hnav_def]; cases waiveUnrealizedLoss with
    | false => rw [if_neg (by decide)]; show 0 ≤ v.withdrawNav
               unfold RawVault.withdrawNav; exact v.exact.withdraw_nav_nonneg
    | true => rw [if_pos rfl]; show 0 ≤ v.depositNav
              unfold RawVault.depositNav; exact v.exact.assetsTotal_nonneg
  have hnav_le_a : nav ≤ a := by
    rw [hnav_def]; cases waiveUnrealizedLoss with
    | false => rw [if_neg (by decide)]
               have hwn : v.withdrawNav = a - l := rfl
               rw [hwn]; linarith
    | true => rw [if_pos rfl]
              have hdn : v.depositNav = a := rfl
              rw [hdn]
  have hnavSlack_eq : v.navSlack = depositε * (a + a) := by
    unfold RawVault.navSlack RawVault.toExact; rw [ha_def]
  have hnavSlack_nn : 0 ≤ v.navSlack := by rw [hnavSlack_eq]; positivity
  have hda_le_slack : depositε * a ≤ v.navSlack := by rw [hnavSlack_eq]; nlinarith [ha_nn, hεnn]
  set ST : ℚ := (v.toExact.sharesTotal : ℚ) with hST_def
  have hST_eq : ST = v.sharesTotal.toRat := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hideal_eq : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat = nav * shares.toRat / ST := rfl
  have hST_nn : 0 ≤ ST := by rw [hST_def]; positivity
  have hideal_nn : 0 ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat := by
    rw [hideal_eq]; exact div_nonneg (mul_nonneg hnav_nonneg hnn) hST_nn
  have hslack_nn : 0 ≤ v.navSlack * shares.toRat / ST :=
    div_nonneg (mul_nonneg hnavSlack_nn hnn) hST_nn
  rcases hcase with ⟨hnav2m, hzero⟩ |
      ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · -- zero payout: the returned amount is the canonical zero
    subst hzero
    have haz : (STAmount.zero v.numericType).toRat = 0 := STAmount.zero_toRat v.numericType
    refine ⟨?_, ?_⟩
    · rw [haz]
      exact mul_nonneg (by linarith [hideal_nn, hslack_nn]) (by linarith [hεnn])
    · intro hf; rw [STAmount.zero_isZero] at hf; exact absurd hf (by decide)
  · -- genuine pricing: run the pipeline against the computed nav2
    have hnav2_nn : 0 ≤ nav2.toRat := by
      cases waiveUnrealizedLoss with
      | true => exact Vault.withdraw_nav2_nonneg v true nav2 hsub
      | false => exact Vault.withdraw_nav2_nonneg v false nav2 hsub
    have hnav2_pos : 0 < nav2.toRat :=
      lt_of_le_of_ne hnav2_nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero nav2 hnav2m))
    have hnav_within : |nav2.toRat - nav| ≤ depositε * a := by
      cases waiveUnrealizedLoss with
      | true => exact Vault.withdraw_nav_within v true nav2 hsub hnav2m
      | false => exact Vault.withdraw_nav_within v false nav2 hsub hnav2m
    obtain ⟨hw_lo, hw_hi⟩ := abs_le.mp hnav_within
    have hnav2norm : nav2.isNormalized := by
      cases waiveUnrealizedLoss with
      | false => exact operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hsub
      | true => exact operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub
    obtain ⟨sn0, hsn0ok, hsn0val, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsn_eq : sn0 = sharesNumber := by rw [hsn0ok] at hsn; exact Except.ok.inj hsn
    have hsnnorm : sharesNumber.isNormalized := by rw [← hsn_eq]; exact hsn0norm
    have hsnval : sharesNumber.toRat = shares.toRat := by rw [← hsn_eq]; exact hsn0val
    -- assets nonzero forces the pipeline mantissas nonzero
    by_cases hzf : assets.isZero = false
    · have hres_ne : assets.mValue ≠ 0 := ne_of_beq_false hzf
      have hanm : assetsNumber.mantissa_ ≠ 0 :=
        STAmount.ofNumber_source_ne_zero v.numericType assetsNumber .downward assets hof hres_ne
      have hST_ne : ¬ v.sharesTotal.operator_eq Number.zero = true := by
        intro heq0; unfold Number.operator_div at hdiv; rw [if_pos heq0] at hdiv; exact absurd hdiv (by simp)
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 := fun h0 =>
        hST_ne (by rw [Number.eq_zero_of_mantissa_zero v.sharesTotal v.wf.sharesTotal_norm h0]; decide)
      have hNAVm : NAVShares.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hdiv hanm
      obtain ⟨hnav2_m', hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
      have hsn_pos : 0 < sharesNumber.toRat := by
        have hsnne : sharesNumber.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero sharesNumber hsn_m
        rw [hsnval] at hsnne ⊢; exact lt_of_le_of_ne hnn (Ne.symm hsnne)
      have hshares_pos : 0 < shares.toRat := by rw [← hsnval]; exact hsn_pos
      have hSTr_pos : 0 < v.sharesTotal.toRat :=
        lt_of_le_of_ne v.wf.sharesTotal_nonneg (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.sharesTotal hSTm))
      have hST_pos : 0 < ST := by rw [hST_eq]; exact hSTr_pos
      obtain ⟨hQnorm, hQpos, hQbound0⟩ :=
        RawVault.exchange_pipeline_within nav2 sharesNumber v.sharesTotal NAVShares assetsNumber
          hnav2norm hsnnorm v.wf.sharesTotal_norm hnav2_pos hsn_pos hSTr_pos hmul hdiv hNAVm hanm
      -- central pipeline value P = nav2 * shares / ST
      rw [hsnval, ← hST_eq] at hQbound0
      set P : ℚ := nav2.toRat * shares.toRat / ST with hP_def
      have hQbound : |assetsNumber.toRat - P| ≤ P * depositε := hQbound0
      have hP_pos : 0 < P := by rw [hP_def]; exact div_pos (mul_pos hnav2_pos hshares_pos) hST_pos
      obtain ⟨hQ_lo, hQ_hi⟩ := abs_le.mp hQbound
      -- downward floor
      have hANneg : assetsNumber.negative_ = false := Number.negative_false_of_pos assetsNumber hQpos
      obtain ⟨hfloor_le, hfloor_ulp, hassets_nn⟩ :=
        STAmount.ofNumber_downward_floor_bounds v.numericType assetsNumber assets hQnorm hANneg hof hres_ne
      -- ideal and slack in the P-frame
      set S : ℚ := v.navSlack * shares.toRat / ST with hS_def
      have hideal_val : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat = nav * shares.toRat / ST := rfl
      have hk_pos : 0 < shares.toRat / ST := div_pos hshares_pos hST_pos
      -- |P - ideal| ≤ S
      have hP_minus_ideal : P - nav * shares.toRat / ST = (nav2.toRat - nav) * (shares.toRat / ST) := by
        rw [hP_def]; ring
      have hPI_le : P - nav * shares.toRat / ST ≤ S := by
        rw [hP_minus_ideal, hS_def]
        have h1 : (nav2.toRat - nav) * (shares.toRat / ST) ≤ depositε * a * (shares.toRat / ST) :=
          mul_le_mul_of_nonneg_right (by linarith [hw_hi]) (le_of_lt hk_pos)
        have h2 : depositε * a * (shares.toRat / ST) ≤ v.navSlack * (shares.toRat / ST) :=
          mul_le_mul_of_nonneg_right hda_le_slack (le_of_lt hk_pos)
        calc (nav2.toRat - nav) * (shares.toRat / ST) ≤ depositε * a * (shares.toRat / ST) := h1
          _ ≤ v.navSlack * (shares.toRat / ST) := h2
          _ = v.navSlack * shares.toRat / ST := by ring
      -- conjunct 1
      refine ⟨?_, ?_⟩
      · rw [hideal_val]
        have hstep : assets.toRat ≤ P * (1 + depositε) := by
          have : assetsNumber.toRat ≤ P + P * depositε := by linarith [hQ_hi]
          calc assets.toRat ≤ assetsNumber.toRat := hfloor_le
            _ ≤ P + P * depositε := this
            _ = P * (1 + depositε) := by ring
        have hPle : P ≤ nav * shares.toRat / ST + S := by linarith [hPI_le]
        calc assets.toRat ≤ P * (1 + depositε) := hstep
          _ ≤ (nav * shares.toRat / ST + S) * (1 + depositε) := by
              apply mul_le_mul_of_nonneg_right hPle (by linarith [hεnn])
      · intro _
        rw [hideal_val]
        have hulp_nn : (0 : ℚ) ≤ (10 : ℚ) ^ assets.exponent := le_of_lt (zpow_pos (by norm_num) _)
        -- assets ≥ P - P*depositε - ulp
        have hassets_lo : P - P * depositε - (10 : ℚ) ^ assets.exponent ≤ assets.toRat := by
          linarith [hQ_lo, hfloor_ulp]
        -- scalar slack budget, linear combination of three sign products
        have hscalar : nav - nav2.toRat + nav2.toRat * depositε ≤ v.navSlack * (1 + depositε) := by
          have e1 : (0 : ℚ) ≤ (nav2.toRat - nav + depositε * a) * (1 - depositε) :=
            mul_nonneg (by linarith [hw_lo]) (by linarith [hεlt])
          have e2 : (0 : ℚ) ≤ depositε * (a - nav) :=
            mul_nonneg hεnn (by linarith [hnav_le_a])
          have e3 : (0 : ℚ) ≤ depositε * depositε * (3 * a) :=
            mul_nonneg (mul_nonneg hεnn hεnn) (by linarith [ha_nn])
          rw [hnavSlack_eq]; nlinarith [e1, e2, e3, hw_lo, hw_hi, hnav_le_a, ha_nn]
        -- multiply by k = shares/ST ≥ 0 and combine
        have hmul_slack : (nav - nav2.toRat + nav2.toRat * depositε) * (shares.toRat / ST)
            ≤ v.navSlack * (1 + depositε) * (shares.toRat / ST) :=
          mul_le_mul_of_nonneg_right hscalar (le_of_lt hk_pos)
        have hSexp : S * (1 + depositε) = v.navSlack * (1 + depositε) * (shares.toRat / ST) := by
          rw [hS_def]; ring
        have hidealexp : nav * shares.toRat / ST - (P - P * depositε)
            = (nav - nav2.toRat + nav2.toRat * depositε) * (shares.toRat / ST) := by
          rw [hP_def]; ring
        have hkey : nav * shares.toRat / ST - (P - P * depositε) ≤ S * (1 + depositε) := by
          rw [hidealexp, hSexp]; exact hmul_slack
        linarith [hassets_lo, hkey, hulp_nn]
    · -- assets is zero: the shortfall conjunct is vacuous, conjunct 1 uses assets = 0
      have haz_true : assets.isZero = true := by
        cases hb : assets.isZero with
        | false => exact absurd hb hzf
        | true => rfl
      have hasset0 : assets.toRat = 0 := by
        have hmv0 : assets.mValue = 0 := by
          have := haz_true; unfold STAmount.isZero at this; exact beq_iff_eq.mp this
        rw [STAmount.toRat_signed, hmv0]; simp
      refine ⟨?_, ?_⟩
      · rw [hasset0]
        exact mul_nonneg (by linarith [hideal_nn, hslack_nn]) (by linarith [hεnn])
      · intro hf; rw [haz_true] at hf; exact absurd hf (by decide)


/-- **A nonzero `sharesToAssetsWithdraw` payout is canonical for its kind.** The
payout packs through `ofNumber v.numericType (NAVShares/sharesTotal) .downward`; its
division source is normalized, so the nonzero output is `IOUCanonical` or
`IntegralCanonical`. Feeds the `10⁻⁸¹` magnitude floor. -/
lemma Vault.sharesToAssetsWithdraw_disj_canonical (v : Vault)
    (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (hc : shares.Canonical)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets)
    (hne : assets.mValue ≠ 0) :
    assets.IOUCanonical ∨ assets.IntegralCanonical := by
  obtain ⟨nav2, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waiveUnrealizedLoss hok
  rcases hcase with ⟨-, hzero⟩ |
      ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · exfalso; rw [hzero, STAmount.zero_mValue] at hne; exact hne rfl
  · have hnav2norm : nav2.isNormalized := by
      cases waiveUnrealizedLoss with
      | false =>
        exact operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hsub
      | true => exact operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub
    obtain ⟨sn0, hsn0ok, -, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsnnorm : sharesNumber.isNormalized := by
      rw [show sharesNumber = sn0 from (Except.ok.inj (hsn0ok.symm.trans hsn)).symm]; exact hsn0norm
    have hanm : assetsNumber.mantissa_ ≠ 0 :=
      STAmount.ofNumber_source_ne_zero v.numericType assetsNumber .downward assets hof hne
    have hST_ne : ¬ v.sharesTotal.operator_eq Number.zero = true := by
      intro h0; unfold Number.operator_div at hdiv; rw [if_pos h0] at hdiv; exact absurd hdiv (by simp)
    have hSTm : v.sharesTotal.mantissa_ ≠ 0 := by
      intro h0
      exact hST_ne (by rw [Number.eq_zero_of_mantissa_zero v.sharesTotal v.wf.sharesTotal_norm h0]; decide)
    have hNAVm : NAVShares.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest hST_ne hdiv hanm
    obtain ⟨hnav2_m', hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
    have hNAVnorm : NAVShares.isNormalized :=
      operator_mul_result_isNormalized nav2 sharesNumber NAVShares .to_nearest
        hnav2norm hsnnorm hnav2_m' hsn_m hmul hNAVm
    have hANnorm : assetsNumber.isNormalized :=
      operator_div_result_isNormalized NAVShares v.sharesTotal assetsNumber .to_nearest
        hNAVnorm v.wf.sharesTotal_norm hNAVm hSTm hdiv hanm
    exact STAmount.ofNumber_disj_canonical v.numericType assetsNumber .downward assets hANnorm hof hne

/-- **Proof body of `Vault.withdraw_vault_updates`.** The withdraw analog of
`clawback_vault_updates`: both asset fields are the stored value minus the payout
within `depositε` (a `to_nearest` subtraction of a nonnegative payout that, when
nonzero, sits `≥ 10⁻⁸¹` on a grid that never underflows the difference to zero), and
the `sharesTotal` update is the exact integer difference on the share domain. -/
theorem Vault.withdraw_vault_updates_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hpnn : 0 ≤ r.assets'.toRat) (hnn : 0 ≤ r.sharesBurned.toRat)
    (hc : r.sharesBurned.Canonical) (hSnt : r.sharesBurned.mNumericType = .int64)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ debitNumber sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' : Number,
      r.assets'.toNumber .to_nearest = .ok debitNumber ∧
      r.sharesBurned.toNumber .to_nearest = .ok sharesBurnedNumber ∧
      v.assetsTotal.operator_sub debitNumber .to_nearest = .ok assetsTotal' ∧
      v.assetsAvailable.operator_sub debitNumber .to_nearest = .ok assetsAvailable' ∧
      v.sharesTotal.operator_sub sharesBurnedNumber .to_nearest = .ok sharesTotal' := by
  obtain ⟨cw, rawN, sbn, debitN, at', av', st', hcomp, herr2, hrawN, havail, hsb,
    hraw, hclamp, hprecision, hdebit, hsbn, hat, hav, hst'⟩ :=
    Vault.withdraw_payout_priced v amount waiveUnrealizedLoss sharesTotalAmount r hok herr hst hfin
  refine ⟨debitN, sbn, at', av', st', hdebit, ?_, hat, hav, hst'⟩
  rw [hsb]
  exact hsbn

/-! ## `withdraw_payout_decreases_assets` -/

/-- **Proof body of `Vault.withdraw_payout_decreases_assets`.** In the non-final
branch both stored asset fields are the old value minus the payout `Number` `aN`,
rounded to nearest. Both never increase (`operator_sub_nonneg_le`, the payout being
non-negative). `assetsTotal` strictly decreases: the precision-loss guard did not
fire on a positive payout, so `ofNumber assetsTotal ≠ ofNumber assetsTotal'`, hence
`assetsTotal' ≠ assetsTotal` (a value tie would make the two `ofNumber` outputs equal
by `Number.isNormalized.toRat_inj`). `assetsAvailable` is left at the weak `≤`: its
strict decrease is a finer-grid tie-exclusion the guard alone does not deliver. -/
theorem Vault.withdraw_payout_decreases_assets_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount)
    (r : WithdrawResult) (hc : r.sharesBurned.Canonical)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hpay : 0 < r.assets'.toRat)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ debitNumber assetsTotal' assetsAvailable' : Number,
      r.assets'.toNumber .to_nearest = .ok debitNumber ∧
      v.assetsTotal.operator_sub debitNumber .to_nearest = .ok assetsTotal' ∧
      v.assetsAvailable.operator_sub debitNumber .to_nearest = .ok assetsAvailable' := by
  obtain ⟨cw, rawN, sbn, debitN, at', av', st', hcomp, herr2, hrawN, havail, hsb,
    hraw, hclamp, hprecision, hdebit, hsbn, hat, hav, hst'⟩ :=
    Vault.withdraw_payout_priced v amount waiveUnrealizedLoss sharesTotalAmount r hok herr hst hfin
  exact ⟨debitN, at', av', hdebit, hat, hav⟩

/-! ## `withdraw_under_available` -/

/-- **Proof body of `Vault.withdraw_under_available`.** The share-denominated
withdrawal prices `shares` into a payout at most the shares' worth times
`1 + depositε`, which the margin hypothesis keeps under `assetsAvailable`; so the
`assetsAvailable` funds guard (the only source of `tecINSUFFICIENT_FUNDS`) cannot
fire, and every other exit reports a different code. -/
theorem Vault.withdraw_under_available_proof (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < shares.toRat) (hc : shares.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    (hmargin : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat *
      (1 + depositε) ≤ v.toExact.assetsAvailable) :
    r.error ≠ some .tecINSUFFICIENT_FUNDS := by
  intro hbad
  unfold Vault.withdraw at hok
  simp only [] at hok
  obtain ⟨result, hres, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : result.error.isSome = true
  · rw [if_pos h1] at hok
    injection hok with h
    rw [← h] at hbad
    rcases computeWithdrawByShares_codes v shares waiveUnrealizedLoss result hres with hc0 | hc0 <;>
      rw [hc0] at hbad <;> simp at hbad
  · rw [if_neg h1] at hok
    have herr2 : result.error = none := by
      cases hce : result.error with
      | none => rfl
      | some t => rw [hce] at h1; exact absurd rfl h1
    try simp only [pure_bind] at hok
    obtain ⟨an, han, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h2 : v.assetsAvailable.operator_lt an = true
    · exfalso
      obtain ⟨hprice, -⟩ :=
        computeWithdrawByShares_none_reduces v shares waiveUnrealizedLoss result hres herr2
      obtain ⟨-, hbound_up, -⟩ :=
        Vault.sharesToAssetsWithdraw_bounds_proof v shares result.assets' waiveUnrealizedLoss
          (le_of_lt hpos) hc hnav hprice
      obtain ⟨hanval, hannorm⟩ :=
        Vault.sharesToAssetsWithdraw_toNumber_facts v shares result.assets' waiveUnrealizedLoss
          an hc hprice han
      have hlt := (operator_lt_iff v.assetsAvailable an v.wf.assetsAvailable_norm hannorm).mp h2
      rw [hanval] at hlt
      have hAA : v.toExact.assetsAvailable = v.assetsAvailable.toRat := rfl
      rw [hAA] at hmargin
      linarith [hbound_up, hmargin, hlt]
    · rw [if_neg h2] at hok
      try simp only [pure_bind] at hok
      obtain ⟨sta, -, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h3 : result.sharesRedeemed.operator_eq sta = true
      · rw [if_pos h3] at hok
        by_cases h4 : v.lossUnrealized.operator_ne Number.zero = true
        · rw [if_pos h4] at hok; injection hok with h; rw [← h] at hbad
          simp [WithdrawResult.rejected] at hbad
        · rw [if_neg h4] at hok
          try simp only [pure_bind] at hok
          obtain ⟨allAvail, -, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨v', -, hok⟩ := bind_ok_peel _ _ _ hok
          injection hok with h; rw [← h] at hbad; simp at hbad
      · rw [if_neg h3] at hok
        obtain ⟨assetDebited, -, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨precision, -, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases hp : precision = true
        · rw [if_pos hp] at hok
          injection hok with h; rw [← h] at hbad
          simp [WithdrawResult.rejected] at hbad
        · rw [if_neg hp] at hok
          obtain ⟨debitN, -, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨sbn, -, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', -, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr, -, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr', -, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases h5 : (debitN.mantissa_ != 0 && atr.operator_eq atr') = true
          · rw [if_pos h5] at hok; injection hok with h; rw [← h] at hbad
            simp [WithdrawResult.rejected] at hbad
          · rw [if_neg h5] at hok
            obtain ⟨av', -, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨st', -, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨v', -, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h] at hbad; simp at hbad

/-! ## `withdraw_final_iff` -/

/-- **`operator_eq` against the stored share total decides value equality.** For a
positive `Int64`-typed canonical burned-shares amount and the round-to-nearest
`ofNumber .int64` of the fitting stored share total, the field-level `operator_eq`
is faithful: it is `true` exactly when the two amounts share a rational value. The
positivity discharges both zero-sign obligations of `CmpFaithful`. -/
lemma Vault.operator_eq_total_iff (v : Vault)
    (sharesTotalAmount sharesBurned : STAmount)
    (hpos : 0 < sharesBurned.toRat) (hc : sharesBurned.Canonical)
    (hSnt : sharesBurned.mNumericType = .int64)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    sharesBurned.operator_eq sharesTotalAmount = true ↔
      sharesBurned.toRat = v.sharesTotal.toRat := by
  have hmv_ne : sharesBurned.mValue ≠ 0 :=
    fun h => (ne_of_gt hpos) ((STAmount.toRat_eq_zero_iff sharesBurned).mpr h)
  obtain ⟨hstaIC, hstaNT⟩ :=
    STAmount.ofNumber_integral_canonical .int64 v.sharesTotal .to_nearest sharesTotalAmount
      (by decide) hst
  have hsta_val : sharesTotalAmount.toRat = v.sharesTotal.toRat :=
    STAmount.ofNumber_integral_exact .int64 v.sharesTotal .to_nearest sharesTotalAmount
      (by decide) v.wf.sharesTotal_norm v.wf.sharesTotal_int hst
  have hsta_sz : sharesTotalAmount.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have h := hstaIC.in_range
    rw [hstaNT] at h
    have hmax : NumericType.int64.maxValue.toNat = 9223372036854775807 := by decide
    rw [hmax] at h
    exact le_trans h (by norm_num)
  have hcmp : STAmount.areComparable sharesBurned sharesTotalAmount = true := by
    simp only [STAmount.areComparable, hSnt, hstaNT, beq_self_eq_true]
  -- with either operand pinned nonzero, `CmpFaithful` decides `operator_eq`
  have mkfaithful : sharesTotalAmount.mValue ≠ 0 →
      sharesBurned.operator_eq sharesTotalAmount
        = decide (sharesBurned.toRat = sharesTotalAmount.toRat) := by
    intro hmv2
    exact STAmount.operator_eq_eq_proof sharesBurned sharesTotalAmount
      (STAmount.CmpFaithful.ofExactCanonical sharesBurned sharesTotalAmount
        (STAmount.Canonical.exactCanonical sharesBurned hc)
        (Or.inr ⟨hstaIC, hsta_sz⟩) hcmp
        (fun h => absurd h hmv_ne) (fun h => absurd h hmv2))
  constructor
  · intro heq
    have hmvq : sharesBurned.mValue = sharesTotalAmount.mValue := by
      unfold STAmount.operator_eq at heq
      exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp heq).2
    have hmv2 : sharesTotalAmount.mValue ≠ 0 := fun h => hmv_ne (hmvq.trans h)
    rw [mkfaithful hmv2, hsta_val] at heq
    exact of_decide_eq_true heq
  · intro hval
    have hmv2 : sharesTotalAmount.mValue ≠ 0 := by
      intro h0
      have hz : sharesTotalAmount.toRat = 0 := (STAmount.toRat_eq_zero_iff sharesTotalAmount).mpr h0
      rw [hsta_val, ← hval] at hz
      exact hpos.ne' hz
    rw [mkfaithful hmv2, hsta_val]
    exact decide_eq_true hval

/-- **A non-final burn leaves a nonzero stored share total.** In the non-final
withdraw branch the stored `sharesTotal'` is the exact integer difference
`sharesTotal - sharesBurned` (both operands `Int64` integers), so it is `Number.zero`
only when the burned shares equal the whole total, which `operator_eq_total_iff`
would report as `true`, contradicting the non-final guard. -/
lemma Vault.sharesTotal_sub_burned_ne_zero (v : Vault)
    (sharesTotalAmount sharesBurned : STAmount) (sbn st' : Number)
    (hpos : 0 < sharesBurned.toRat) (hc : sharesBurned.Canonical)
    (hSnt : sharesBurned.mNumericType = .int64)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : sharesBurned.operator_eq sharesTotalAmount = false)
    (hsbn : sharesBurned.toNumber .to_nearest = .ok sbn)
    (hst2 : v.sharesTotal.operator_sub sbn .to_nearest = .ok st') :
    st' ≠ Number.zero := by
  intro h0
  -- `sbn` is value-exact and normalized
  obtain ⟨sbn0, hsbn0ok, hsbn0val, hsbn0norm⟩ :=
    STAmount.toNumber_canonical_exact sharesBurned .to_nearest hc
  have hsbn_eq : sbn0 = sbn := Except.ok.inj (hsbn0ok.symm.trans hsbn)
  have hsbn_val : sbn.toRat = sharesBurned.toRat := by rw [← hsbn_eq]; exact hsbn0val
  have hsbn_norm : sbn.isNormalized := by rw [← hsbn_eq]; exact hsbn0norm
  -- burned shares are a bounded nonnegative integer
  have hint_sb : sharesBurned.integral = true := by
    show sharesBurned.mNumericType.isIntegral = true; rw [hSnt]; decide
  obtain ⟨hic, hmax⟩ := hc.1 hint_sb
  have hkden : sharesBurned.toRat.den = 1 := STAmount.IntegralCanonical.den_eq_one sharesBurned hic
  have hsb_le : sharesBurned.toRat ≤ 2 ^ 63 - 1 := by
    rw [STAmount.IntegralCanonical.toRat_eq_signedDrops sharesBurned hic]
    have hmv_le : sharesBurned.mValue.toNat ≤ 9223372036854775807 := by
      calc sharesBurned.mValue.toNat ≤ sharesBurned.mNumericType.maxValue.toNat := hic.in_range
        _ ≤ maxRep.toNat := hmax
        _ = 9223372036854775807 := maxRep_val
    have hsd_le : sharesBurned.signedDrops ≤ (sharesBurned.mValue.toNat : ℤ) := by
      unfold STAmount.signedDrops
      rcases sharesBurned.mIsNegative <;> simp
    calc (sharesBurned.signedDrops : ℚ) ≤ (sharesBurned.mValue.toNat : ℚ) := by exact_mod_cast hsd_le
      _ ≤ 2 ^ 63 - 1 := by
          rw [show (2 : ℚ) ^ 63 - 1 = ((9223372036854775807 : ℕ) : ℚ) from by norm_num]
          exact_mod_cast hmv_le
  -- the difference fits the integer domain
  have hdden : (v.sharesTotal.toRat - sharesBurned.toRat).den = 1 := by
    rw [wb_eq_intCast_of_den_one v.wf.sharesTotal_int, wb_eq_intCast_of_den_one hkden,
      ← Int.cast_sub]
    exact Rat.den_intCast _
  have hdnum_q : ((v.sharesTotal.toRat - sharesBurned.toRat).num : ℚ)
      = v.sharesTotal.toRat - sharesBurned.toRat := (wb_eq_intCast_of_den_one hdden).symm
  have hlo' : -(2 ^ 63 - 1 : ℤ) ≤ (v.sharesTotal.toRat - sharesBurned.toRat).num := by
    have h : (-(2 ^ 63 - 1 : ℤ) : ℚ) ≤ ((v.sharesTotal.toRat - sharesBurned.toRat).num : ℚ) := by
      rw [hdnum_q]; push_cast; linarith [v.wf.sharesTotal_nonneg, hsb_le]
    exact_mod_cast h
  have hhi' : (v.sharesTotal.toRat - sharesBurned.toRat).num ≤ (2 ^ 63 - 1 : ℤ) := by
    have h : ((v.sharesTotal.toRat - sharesBurned.toRat).num : ℚ) ≤ (2 ^ 63 - 1 : ℤ) := by
      rw [hdnum_q]; push_cast; linarith [le_of_lt hpos, hfit]
    exact_mod_cast h
  have hbound : (v.sharesTotal.toRat - sharesBurned.toRat).num.natAbs < 2 ^ 63 := by omega
  obtain ⟨hst_val, -⟩ :=
    operator_sub_exact_int v.sharesTotal sbn st' v.wf.sharesTotal_norm hsbn_norm
      v.wf.sharesTotal_int (by rw [hsbn_val]; exact hkden) (by rw [hsbn_val]; exact hbound) hst2
  have hval_eq : sharesBurned.toRat = v.sharesTotal.toRat := by
    have hz : st'.toRat = 0 := by rw [h0]; exact Number.toRat_zero
    rw [hst_val, hsbn_val] at hz; linarith
  have heq_true :=
    (Vault.operator_eq_total_iff v sharesTotalAmount sharesBurned hpos hc hSnt hst).mpr hval_eq
  exact absurd (hfin.symm.trans heq_true) (by decide)

/-- **Proof body of `Vault.withdraw_final_iff`.** The forward direction is the two-way
case split of the success reduction; the backward direction rules out the non-final
branch by `sharesTotal_sub_burned_ne_zero`. -/
theorem Vault.withdraw_final_iff_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool)
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    r.sharesBurned.operator_eq sharesTotalAmount = true ↔
      r.vault'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  obtain ⟨cw, an', sta, hcomp, herr2, han, hlt, hsta, hsb, hdisj⟩ :=
    Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr
  have hsta_eq : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  -- the stored share total fits `Int64` because its `ofNumber .int64` succeeded
  obtain ⟨hstaIC, hstaNT⟩ :=
    STAmount.ofNumber_integral_canonical .int64 v.sharesTotal .to_nearest sharesTotalAmount
      (by decide) hst
  have hsta_val : sharesTotalAmount.toRat = v.sharesTotal.toRat :=
    STAmount.ofNumber_integral_exact .int64 v.sharesTotal .to_nearest sharesTotalAmount
      (by decide) v.wf.sharesTotal_norm v.wf.sharesTotal_int hst
  have hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by
    rw [← hsta_val, STAmount.IntegralCanonical.toRat_eq_signedDrops sharesTotalAmount hstaIC]
    have hmv_le : sharesTotalAmount.mValue.toNat ≤ 9223372036854775807 := by
      have h := hstaIC.in_range
      rw [hstaNT] at h
      calc sharesTotalAmount.mValue.toNat ≤ NumericType.int64.maxValue.toNat := h
        _ = 9223372036854775807 := by decide
    have hsd_le : sharesTotalAmount.signedDrops ≤ (sharesTotalAmount.mValue.toNat : ℤ) := by
      unfold STAmount.signedDrops
      rcases sharesTotalAmount.mIsNegative <;> simp
    calc (sharesTotalAmount.signedDrops : ℚ) ≤ (sharesTotalAmount.mValue.toNat : ℚ) := by
          exact_mod_cast hsd_le
      _ ≤ 2 ^ 63 - 1 := by
          rw [show (2 : ℚ) ^ 63 - 1 = ((9223372036854775807 : ℕ) : ℚ) from by norm_num]
          exact_mod_cast hmv_le
  constructor
  · intro heq
    rcases hdisj with ⟨-, -, allAvail, -, -, hr⟩ | ⟨hfin, -⟩
    · rw [hr]
    · exfalso
      rw [hsb] at heq; rw [← hsta_eq] at heq
      exact absurd (hfin.symm.trans heq) (by decide)
  · intro hvault
    rcases hdisj with ⟨hfin, -, -, -, -⟩ |
        ⟨hfin, sbn, debitN, at', av', st', debit, atr, atr', hsbn, hclamp, hprecision,
          hdebit, hat, hatr, hatr', hg, hav, hst2, -, hr⟩
    · rw [hsb, ← hsta_eq]; exact hfin
    · exfalso
      have hrv : r.vault'.toRawVault =
          { v with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := hr
      have hst_zero : st' = Number.zero := congrArg RawVault.sharesTotal (hrv.symm.trans hvault)
      have hfin' : r.sharesBurned.operator_eq sharesTotalAmount = false := by
        rw [hsb, ← hsta_eq]; exact hfin
      have hsbn' : r.sharesBurned.toNumber .to_nearest = .ok sbn := by rw [hsb]; exact hsbn
      exact Vault.sharesTotal_sub_burned_ne_zero v sharesTotalAmount r.sharesBurned sbn st'
        hpos hc hSnt hfit hst hfin' hsbn' hst2 hst_zero

/-! ## `withdraw_final_payout` -/

/-- **The 16-digit ULP is monotone in the payout value.** Two non-negative canonical
amounts of the same numeric type keep `exponent` (`= mOffset`) order under value order:
integral amounts share offset `0`, fractional amounts are 16-digit banded, so a larger
exponent forces a larger magnitude. -/
lemma RawVault.payout_exponent_le (rv : RawVault) (a b : STAmount)
    (hnt_a : a.mNumericType = rv.numericType) (hnt_b : b.mNumericType = rv.numericType)
    (hca : a.IOUCanonical ∨ a.IntegralCanonical) (hcb : b.IOUCanonical ∨ b.IntegralCanonical)
    (hann : 0 ≤ a.toRat) (hbnn : 0 ≤ b.toRat) (hle : a.toRat ≤ b.toRat) :
    (10 : ℚ) ^ a.exponent ≤ (10 : ℚ) ^ b.exponent := by
  have hoff : a.mOffset ≤ b.mOffset := by
    by_contra hlt
    push_neg at hlt
    by_cases hint : rv.numericType.isIntegral = true
    · have ha0 : a.mOffset = 0 := (hca.resolve_left (fun hio => by
        have h1 : a.mNumericType = .fractional := hio.is_fractional
        rw [hnt_a] at h1; rw [h1] at hint; exact absurd hint (by decide))).offset_zero
      have hb0 : b.mOffset = 0 := (hcb.resolve_left (fun hio => by
        have h1 : b.mNumericType = .fractional := hio.is_fractional
        rw [hnt_b] at h1; rw [h1] at hint; exact absurd hint (by decide))).offset_zero
      rw [ha0, hb0] at hlt; exact absurd hlt (lt_irrefl 0)
    · have hfr : rv.numericType = .fractional := by
        cases hnt : rv.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt] at hint; exact absurd rfl hint
      have haIou : a.IOUCanonical := hca.resolve_right (fun hii => by
        have h1 := hii.is_integral; rw [hnt_a, hfr] at h1; exact absurd h1 (by decide))
      have hbIou : b.IOUCanonical := hcb.resolve_right (fun hii => by
        have h1 := hii.is_integral; rw [hnt_b, hfr] at h1; exact absurd h1 (by decide))
      have hcontra := STAmount.abs_lt_of_offset_lt b a ⟨hbIou.mant_lo, hbIou.mant_hi⟩
        ⟨haIou.mant_lo, haIou.mant_hi⟩ hlt
      rw [abs_of_nonneg hbnn, abs_of_nonneg hann] at hcontra
      linarith [hle]
  exact zpow_le_zpow_right₀ (by norm_num) (show a.exponent ≤ b.exponent from hoff)

/-- **Proof body of `Vault.withdraw_final_payout`.** The final branch pays `allAvailable
= ofNumber assetsAvailable`, which the `assetsAvailable`-canonicity hypothesis keeps exact.
Burning the whole share total makes the ideal collapse to the pricing `nav`, and lawful
`assetsAvailable ≤ nav` gives the upper bound. The lower bound squeezes the payout between
the funds guard (`priced ≤ assetsAvailable`) and the `sharesToAssetsWithdraw` accuracy
window, with the ULP compared through `payout_exponent_le`. -/
theorem Vault.withdraw_final_payout_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hfinal : r.vault'.sharesTotal = Number.zero)
    (hAAc : ∀ aa : STAmount,
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok aa →
        aa.toRat = v.assetsAvailable.toRat) :
    r.assets'.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat ∧
    (0 < v.toExact.assetsAvailable →
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 - depositε) -
        2 * (10 : ℚ) ^ r.assets'.exponent ≤ r.assets'.toRat) := by
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hεlt : depositε < 1 := by rw [depositε_eq]; norm_num
  obtain ⟨cw, an', sta, hcomp, herr2, han, hlt, hsta, hsb, hdisj⟩ :=
    Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr
  have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by
    -- the internal `ofNumber .int64 v.sharesTotal` success bounds the share total
    have hic := STAmount.ofNumber_integral_canonical .int64 v.sharesTotal .to_nearest sta
      (by decide) hsta
    have hex := STAmount.ofNumber_integral_exact .int64 v.sharesTotal .to_nearest sta
      (by decide) v.wf.sharesTotal_norm v.wf.sharesTotal_int hsta
    have hle := STAmount.IntegralCanonical.abs_toRat_le sta hic.1
    rw [hic.2, show (NumericType.int64.maxValue).toNat = 9223372036854775807 from by decide] at hle
    rw [← hex]
    calc sta.toRat ≤ |sta.toRat| := le_abs_self _
      _ ≤ (9223372036854775807 : ℚ) := by exact_mod_cast hle
      _ = 2 ^ 63 - 1 := by norm_num
  -- pricing of the payout `cw.assets'`
  have hstw : v.sharesToAssetsWithdraw cw.sharesRedeemed waiveUnrealizedLoss = .ok cw.assets' := by
    cases amount with
    | vaultAssets a =>
      obtain ⟨sh, -, -, hs, hsr⟩ :=
        computeWithdrawByAssets_none_reduces v a waiveUnrealizedLoss cw hcomp herr2
      rw [hsr]; exact hs
    | vaultShares s =>
      obtain ⟨hs, hsr⟩ :=
        computeWithdrawByShares_none_reduces v s waiveUnrealizedLoss cw hcomp herr2
      rw [hsr]; exact hs
  rcases hdisj with ⟨hfin, hloss, allAvail, hallAvail, hra0, hr⟩ |
      ⟨hfin_nf, sbn, debitN, at', av', st', debit, atr, atr', hsbn, hclamp, hprecision,
          hdebit, hat, hatr, hatr', hg, hav, hst2, -, hr_nf⟩
  swap
  · -- non-final branch is ruled out by `hfinal`
    exfalso
    have hrv : r.vault'.toRawVault =
        { v with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := hr_nf
    have hst_zero : st' = Number.zero :=
      (congrArg RawVault.sharesTotal hrv).symm.trans hfinal
    exact Vault.sharesTotal_sub_burned_ne_zero v sta r.sharesBurned sbn st'
      hpos hc hSnt hfit' hsta (by rw [hsb]; exact hfin_nf) (by rw [hsb]; exact hsbn) hst2 hst_zero
  -- final branch
  have hra : r.assets' = allAvail := hra0
  have hsb_eq_red : cw.sharesRedeemed = r.sharesBurned := hsb.symm
  -- burned shares equal the whole stored total
  have hSb_eq : r.sharesBurned.toRat = v.sharesTotal.toRat :=
    (Vault.operator_eq_total_iff v sta r.sharesBurned hpos hc hSnt hsta).mp
      (by rw [hsb]; exact hfin)
  have hST_pos : 0 < v.sharesTotal.toRat := hSb_eq ▸ hpos
  have hST_eq : (v.toExact.sharesTotal : ℚ) = v.sharesTotal.toRat := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  -- the unrealized loss is zero on the final branch
  have hloss_val : v.lossUnrealized.toRat = 0 := by
    by_contra hne
    have hne' : v.lossUnrealized.operator_ne Number.zero = true :=
      (operator_ne_iff v.lossUnrealized Number.zero v.wf.lossUnrealized_norm (Or.inl rfl)).mpr
        (by rw [Number.toRat_zero]; exact hne)
    rw [hne'] at hloss; exact absurd hloss (by decide)
  -- the pricing `nav` and the collapsed ideal
  set nav : ℚ := (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) with hnav_def
  have hnav_eq_ai : nav = v.toExact.assetsTotal := by
    rw [hnav_def]; cases waiveUnrealizedLoss with
    | false =>
      rw [if_neg (by decide)]; unfold RawVault.withdrawNav
      rw [show v.toExact.lossUnrealized = 0 from hloss_val]; ring
    | true => rw [if_pos rfl]; rfl
  have hideal_eq : v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat = nav := by
    unfold RawVault.idealAssetsWithdraw
    rw [← hnav_def, hSb_eq, hST_eq, mul_div_assoc, div_self hST_pos.ne', mul_one]
  -- `nav` is non-negative and dominates `assetsAvailable`
  have hAA_nn : 0 ≤ v.toExact.assetsAvailable := v.exact.assetsAvailable_nonneg
  have hAA_le_nav : v.toExact.assetsAvailable ≤ nav := by
    rw [hnav_eq_ai]; exact v.exact.assetsAvailable_le
  have hnav_nn : 0 ≤ nav := le_trans hAA_nn hAA_le_nav
  -- the paid amount is exactly `assetsAvailable`
  have haa_val : allAvail.toRat = v.toExact.assetsAvailable := hAAc allAvail hallAvail
  have hpaid : r.assets'.toRat = v.toExact.assetsAvailable := by rw [hra]; exact haa_val
  -- upper bound
  have hupper : r.assets'.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat := by
    rw [hideal_eq, hpaid]; exact hAA_le_nav
  refine ⟨hupper, ?_⟩
  intro hAApos
  rw [hideal_eq, hpaid]
  -- funds guard: the priced payout is under `assetsAvailable`
  obtain ⟨hanval, hannorm⟩ :=
    Vault.sharesToAssetsWithdraw_toNumber_facts v cw.sharesRedeemed cw.assets' waiveUnrealizedLoss
      an' (hsb ▸ hc) hstw han
  have hpriced_le : cw.assets'.toRat ≤ v.toExact.assetsAvailable := by
    have hnot : ¬ (v.assetsAvailable.toRat < an'.toRat) := fun hcmp =>
      absurd (((operator_lt_iff v.assetsAvailable an' v.wf.assetsAvailable_norm hannorm).mpr hcmp).symm.trans hlt)
        (by decide)
    rw [hanval] at hnot
    exact not_lt.mp hnot
  -- accuracy window of the priced payout
  obtain ⟨hprice_nn, hideal_price_nn, -, hprice_short⟩ :=
    Vault.sharesToAssetsWithdraw_spec v cw.sharesRedeemed cw.assets' waiveUnrealizedLoss
      (le_of_lt (hsb_eq_red ▸ hpos)) (hsb ▸ hc) hnav hstw
  have hideal_price_eq : v.idealAssetsWithdraw waiveUnrealizedLoss cw.sharesRedeemed.toRat = nav := by
    rw [hsb_eq_red]; exact hideal_eq
  rw [hideal_price_eq] at hprice_short hideal_price_nn
  by_cases hzp : cw.assets'.isZero = false
  · -- nonzero priced payout: the interior-stage window plus the ULP swap
    have hshort := hprice_short hzp
    -- both payouts are nonzero canonical amounts of `v.numericType`
    have hcw_ne : cw.assets'.mValue ≠ 0 := ne_of_beq_false hzp
    have hcw_ne0 : cw.assets'.toRat ≠ 0 :=
      fun h => hcw_ne ((STAmount.toRat_eq_zero_iff cw.assets').mp h)
    have hcw_pos : 0 < cw.assets'.toRat := lt_of_le_of_ne hprice_nn (Ne.symm hcw_ne0)
    have hAA_pos : 0 < v.toExact.assetsAvailable := lt_of_lt_of_le hcw_pos hpriced_le
    have hallAvail_ne : allAvail.mValue ≠ 0 := by
      intro h0
      have : allAvail.toRat = 0 := (STAmount.toRat_eq_zero_iff allAvail).mpr h0
      rw [haa_val] at this; linarith [hAA_pos]
    have hcw_nt : cw.assets'.mNumericType = v.numericType :=
      Vault.sharesToAssetsWithdraw_mNumericType v cw.sharesRedeemed cw.assets' waiveUnrealizedLoss hstw
    have haa_nt : allAvail.mNumericType = v.numericType :=
      STAmount.ofNumber_mNumericType v.numericType v.assetsAvailable .to_nearest allAvail hallAvail
    have hcw_can : cw.assets'.IOUCanonical ∨ cw.assets'.IntegralCanonical :=
      Vault.sharesToAssetsWithdraw_disj_canonical v cw.sharesRedeemed cw.assets'
        waiveUnrealizedLoss (hsb ▸ hc) hstw hcw_ne
    have haa_can : allAvail.IOUCanonical ∨ allAvail.IntegralCanonical :=
      STAmount.ofNumber_disj_canonical v.numericType v.assetsAvailable .to_nearest allAvail
        v.wf.assetsAvailable_norm hallAvail hallAvail_ne
    have hexp_le : (10 : ℚ) ^ cw.assets'.exponent ≤ (10 : ℚ) ^ allAvail.exponent :=
      RawVault.payout_exponent_le v.toRawVault cw.assets' allAvail hcw_nt haa_nt hcw_can haa_can
        hprice_nn (haa_val ▸ le_of_lt hAA_pos) (haa_val ▸ hpriced_le)
    have hexp_pos : (0 : ℚ) < (10 : ℚ) ^ allAvail.exponent := zpow_pos (by norm_num) _
    have hrexp : r.assets'.exponent = allAvail.exponent := by rw [hra]
    rw [hrexp]
    -- combine: nav*(1-ε) - AA ≤ (nav - priced) - nav*ε ≤ 10^cw.exp ≤ 10^allAvail.exp
    have hkey : nav * (1 - depositε) - v.toExact.assetsAvailable ≤ (10 : ℚ) ^ cw.assets'.exponent := by
      have h1 : nav - cw.assets'.toRat ≤ nav * depositε + (10 : ℚ) ^ cw.assets'.exponent := hshort
      nlinarith [hpriced_le, h1]
    calc nav * (1 - depositε) - 2 * (10 : ℚ) ^ allAvail.exponent
        ≤ nav * (1 - depositε) - 2 * (10 : ℚ) ^ cw.assets'.exponent := by
          have : (10 : ℚ) ^ cw.assets'.exponent ≤ (10 : ℚ) ^ allAvail.exponent := hexp_le
          linarith
      _ ≤ v.toExact.assetsAvailable := by
          have hcwexp_pos : (0 : ℚ) < (10 : ℚ) ^ cw.assets'.exponent := zpow_pos (by norm_num) _
          linarith [hkey, hcwexp_pos]
  · -- Zero priced payout: `sharesToAssetsWithdraw` floored the whole-share price to `0`,
    -- so the exact worth `nav` is below the smallest representable value of the vault's
    -- numeric type. With `assetsAvailable` positive (the gate `hAApos`) the paid amount
    -- `allAvail` is a nonzero canonical amount, hence at least that smallest value, and
    -- the lower bound is immediate. The excluded `assetsAvailable = 0` corner would pay
    -- the zero record (`mOffset = -100`), whose `2` ULP slack `2·10⁻¹⁰⁰` is finer than
    -- `nav` can be (up to `10⁻⁸¹` fractional), which is why the bound is gated.
    have hzmv : cw.assets'.mValue = 0 := by
      have h : cw.assets'.isZero = true := by
        cases hb : cw.assets'.isZero with
        | true => rfl
        | false => exact absurd hb hzp
      unfold STAmount.isZero at h; exact beq_iff_eq.mp h
    have hnav_pos : 0 < nav := lt_of_lt_of_le hAApos hAA_le_nav
    have hnav_pos_if : 0 < (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
      rw [← hnav_def]; exact hnav_pos
    have hmul_nn : 0 ≤ nav * depositε := mul_nonneg (le_of_lt hnav_pos) hεnn
    have hrexp_pos : (0 : ℚ) < 2 * (10 : ℚ) ^ r.assets'.exponent := by positivity
    -- the paid amount is a nonzero canonical amount of `v.numericType`
    have hallAvail_ne : allAvail.mValue ≠ 0 := by
      intro h0
      have hz0 : allAvail.toRat = 0 := (STAmount.toRat_eq_zero_iff allAvail).mpr h0
      rw [haa_val] at hz0; linarith [hAApos]
    have haa_can : allAvail.IOUCanonical ∨ allAvail.IntegralCanonical :=
      STAmount.ofNumber_disj_canonical v.numericType v.assetsAvailable .to_nearest allAvail
        v.wf.assetsAvailable_norm hallAvail hallAvail_ne
    have haa_nt : allAvail.mNumericType = v.numericType :=
      STAmount.ofNumber_mNumericType v.numericType v.assetsAvailable .to_nearest allAvail hallAvail
    -- `nav` bound from the zero priced payout
    obtain ⟨aN, hof, hnzcase, hzcase⟩ :=
      Vault.recovery_pipeline_bound_gen v cw.sharesRedeemed cw.assets' waiveUnrealizedLoss
        hnav (hsb ▸ hc) hnav_pos_if (hsb_eq_red ▸ hpos) hstw
    rw [hideal_price_eq] at hnzcase hzcase
    have heq : nav * (1 - depositε) = nav - nav * depositε := by ring
    by_cases hint : v.numericType.isIntegral = true
    · -- integral: `assetsAvailable ≥ 1` and `nav·(1-ε) ≤ 1`
      have haa_int : allAvail.IntegralCanonical := haa_can.resolve_left (fun hio => by
        have h1 : allAvail.mNumericType = .fractional := hio.is_fractional
        rw [haa_nt] at h1; rw [h1] at hint; exact absurd hint (by decide))
      have haa_ge1 : (1 : ℚ) ≤ v.toExact.assetsAvailable := by
        have hval : allAvail.toRat = (allAvail.signedDrops : ℚ) :=
          STAmount.toRat_of_offset_zero allAvail haa_int.offset_zero
        have hsd_pos : 0 < allAvail.signedDrops := by
          have hq : (0 : ℚ) < (allAvail.signedDrops : ℚ) := by
            rw [← hval, haa_val]; exact hAApos
          exact_mod_cast hq
        have hsd1 : (1 : ℤ) ≤ allAvail.signedDrops := by omega
        rw [← haa_val, hval]; exact_mod_cast hsd1
      have hnav_le1 : nav * (1 - depositε) ≤ 1 := by
        rw [heq]
        by_cases haN0 : aN.mantissa_ = 0
        · have hsmall := hzcase haN0
          have hle1 : (10 : ℚ) ^ (-32700 : ℤ) ≤ 1 := by
            calc (10 : ℚ) ^ (-32700 : ℤ) ≤ (10 : ℚ) ^ (0 : ℤ) :=
                  zpow_le_zpow_right₀ (by norm_num) (by norm_num)
              _ = 1 := by norm_num
          linarith [hsmall, hle1, hmul_nn]
        · obtain ⟨haNnorm, haNneg, hbound⟩ := hnzcase haN0
          have haN1 : aN.toRat < 1 :=
            STAmount.ofNumber_integral_zero_floor v.numericType aN cw.assets' hint haNnorm haNneg hof hzmv
          linarith [hbound, haN1]
      linarith [haa_ge1, hnav_le1, hrexp_pos]
    · -- fractional: `assetsAvailable ≥ 10⁻⁸¹` and `nav·(1-ε) ≤ 10⁻⁸¹`
      have hfr : v.numericType.isIntegral = false := by
        cases h : v.numericType.isIntegral with
        | true => exact absurd h hint
        | false => rfl
      have haa_ge : (10 : ℚ) ^ (-81 : ℤ) ≤ v.toExact.assetsAvailable := by
        have hge := STAmount.canonical_disj_abs_toRat_ge allAvail haa_can hallAvail_ne
        rwa [abs_of_nonneg (by rw [haa_val]; exact le_of_lt hAApos), haa_val] at hge
      have hnav_le : nav * (1 - depositε) ≤ (10 : ℚ) ^ (-81 : ℤ) := by
        rw [heq]
        by_cases haN0 : aN.mantissa_ = 0
        · have hsmall := hzcase haN0
          have hle81 : (10 : ℚ) ^ (-32700 : ℤ) ≤ (10 : ℚ) ^ (-81 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by norm_num)
          linarith [hsmall, hle81, hmul_nn]
        · obtain ⟨haNnorm, haNneg, hbound⟩ := hnzcase haN0
          have haNfloor : aN.toRat < (10 : ℚ) ^ (-81 : ℤ) :=
            STAmount.ofNumber_fractional_zero_below_min v.numericType aN cw.assets' hfr haNnorm
              haNneg haN0 hof hzmv
          linarith [hbound, haNfloor]
      linarith [haa_ge, hnav_le, hrexp_pos]

end XRPL.Model.SingleAssetVault
