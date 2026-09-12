import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.Number.Mul.Common.Decompose
import XRPL.Properties.Protocol.Number.Div.Common.Decompose

/-! # `Vault.deposit` charge accuracy proofs

Proof bodies for the charge-side accuracy headlines in `VaultDeposit.lean`
(`deposit_charge`, `deposit_charge_integral`). The charge
`sharesToAssetsDeposit` prices the issued shares back into the asset by the
three-stage `sub`/`mul`/`div` pipeline followed by an upward `ofNumber` snap.

This file lives downstream of `OfNumberBoundary` because the charge bound needs
the success-keyed exponent-range dischargers there, plus `to_rep_nonneg_range`
(from `WithdrawAccuracy`) and the unconditional `operator_sub` shape lemmas
(from `LawfulSupport`). -/

namespace XRPL.Model.Protocol

/-- **`ofNumber` on an integral type rounds within one unit** of a sign-cleared
normalized `Number`. The integral packing routes the magnitude through `to_rep`,
which lands within one of the value; a non-negative source keeps the sign bit
clear so the stored value is exactly the `to_rep` integer. -/
lemma STAmount.ofNumber_integral_within_one (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount)
    (hnt : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    |result.toRat - n.toRat| < 1 := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hnt] at hok
  cases hr : n.to_rep mode with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ :=
      XRPL.Model.SingleAssetVault.Number.to_rep_nonneg_range n mode intValue hneg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    have hres : result.toRat = (intValue.toInt : ℚ) := by
      have hexact := STAmount.canonicalize_integral_toRat
        (STAmount.unchecked nt intValue.toUInt64 0 false) result mode
        (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hnt) rfl
        hval hok
      rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
      show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
      rw [toUInt64_toNat_of_nonneg intValue hnn]
    rw [hres]
    exact to_rep_within_one n mode intValue hn hr

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The combined `sub`+`mul` relative error of the charge numerator stays within
the clean bound `12 / (2^63 - 3)`. -/
lemma charge_eps2_bound :
    (1 + 6 / (2 ^ 63 - 3 : ℚ)) * (5 / (2 ^ 63 + 7)) + 6 / (2 ^ 63 - 3) ≤ 12 / (2 ^ 63 - 3) := by
  norm_num

/-- Upper closure of the charge `sub`/`mul`/`div` pipeline within `depositε`. -/
lemma charge_pipeline_up :
    ((1 : ℚ) + 12 / (2 ^ 63 - 3)) * (1 + 6 / (2 ^ 63 - 3))
      ≤ (1 + depositε) * (1 - 0) := by
  rw [depositε_eq]; norm_num

/-- Lower closure of the charge `sub`/`mul`/`div` pipeline within `depositε`. -/
lemma charge_pipeline_lo :
    ((1 : ℚ) - depositε) * (1 + 0)
      ≤ (1 - 12 / (2 ^ 63 - 3)) * (1 - 6 / (2 ^ 63 - 3)) := by
  rw [depositε_eq]; norm_num

/-- Cross-multiplied upper bound: a quotient's numerator error bounds the quotient
above by the exact ratio times `(1 + ε)`. Kept abstract so the arithmetic solvers
never unfold the `depositNav`/`sharesTotal` rationals. -/
private lemma charge_div_upper (A B D ε : ℚ) (hD : 0 < D) (h : |A * D - B| ≤ B * ε) :
    A ≤ B / D * (1 + ε) := by
  have hab := abs_le.mp h
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  nlinarith [hab.2]

/-- Ceiling combine: a value within `+1` of `Q ≤ I·(1+ε)` overshoots `I` by at most
`1 + I·ε`. Abstract so the solver stays off the vault rationals. -/
private lemma charge_ceiling (I Q c ε : ℚ) (hQ : Q ≤ I * (1 + ε)) (hc : c ≤ Q + 1) :
    c - I ≤ 1 + I * ε := by nlinarith

/-- **Integral charge overcharge bound.** On a lawful integral vault the taken
amount `c = sharesToAssetsDeposit v shares` overshoots the exact charge by less
than one whole unit plus the relative stage error: the empty branch is exact, and
the nonempty branch is `⌈nav·shares/sharesTotal⌉` (upward `ofNumber`), whose
integer ceiling adds at most `1` on top of the `depositε` pipeline error. -/
lemma sharesToAssetsDeposit_charge_integral_bound (v : Vault) (_amount shares c : STAmount)
    (hint : v.numericType.isIntegral = true)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    0 ≤ v.idealChargeDeposit shares.toRat ∧
    c.toRat - v.idealChargeDeposit shares.toRat ≤
      1 + v.idealChargeDeposit shares.toRat * depositε := by
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hshmax : shares.mValue.toNat ≤ maxRep.toNat := by
    have hr := hshc.in_range; rw [hshnt] at hr
    calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
      _ = maxRep.toNat := by decide
  obtain ⟨hcc, hcnt⟩ := sharesToAssetsDeposit_integral_canonical v shares c hint hsad
  unfold sharesToAssetsDeposit at hsad
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: `c = shares` exactly, `idealCharge = shares` (scale 0)
    have hA0 : v.toExact.assetsTotal = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal hmz
    have hscale : v.scale = 0 := v.wf.scale_integral hint
    have hshexp : shares.exponent = 0 := hshc.offset_zero
    have hideal : v.idealChargeDeposit shares.toRat = shares.toRat := by
      unfold RawVault.idealChargeDeposit
      rw [if_pos hA0, hscale]
      show shares.toRat / (10 : ℚ) ^ (0 : UInt8).toNat = shares.toRat
      norm_num
    rw [if_pos hmz] at hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    rw [STAmount.checked] at hc
    have hoff0 : (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
      show shares.exponent - (v.scale.toNat : ℤ) = 0
      rw [hshexp, hscale]; rfl
    have hval0 : (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := by
      show shares.mantissa.toNat ≤ maxRep.toNat
      exact hshmax
    have hcval := STAmount.canonicalize_integral_toRat _ c .to_nearest
      (show (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff0 hval0 hc
    have hun : (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).toRat = (shares.mValue.toNat : ℚ) := by
      rw [STAmount.toRat_of_offset_zero
        (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false) hoff0]
      unfold STAmount.signedDrops STAmount.unchecked STAmount.mantissa
      simp
    have hsh : shares.toRat = (shares.mValue.toNat : ℚ) := by
      rw [STAmount.toRat_of_offset_zero shares hshexp]
      unfold STAmount.signedDrops
      rw [STAmount.mIsNegative_false_of_pos shares hshpos]
      simp
    have hcshares : c.toRat = shares.toRat := by rw [hcval, hun, hsh]
    rw [hideal, hcshares]
    refine ⟨le_of_lt hshpos, ?_⟩
    have : (0 : ℚ) ≤ shares.toRat * depositε := mul_nonneg (le_of_lt hshpos) hεnn
    linarith
  · -- nonempty vault: three-stage pipeline into an upward `ofNumber`
    set nav : ℚ := v.depositNav with hnav_def
    set s : ℚ := shares.toRat with hs_def
    set ST : ℚ := v.sharesTotal.toRat with hST_def
    have hApos : 0 < v.toExact.assetsTotal := by
      rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
      · exact h
      · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
    have hnav_pos : 0 < nav := by
      rw [hnav_def]; unfold RawVault.depositNav; exact hApos
    have hST_pos : 0 < ST := by
      have hne : v.toExact.sharesTotal ≠ 0 := by
        intro h0
        exact absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
      have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
      have : (0 : ℚ) < (v.toExact.sharesTotal : ℚ) := by
        have : 0 < v.toExact.sharesTotal := Nat.pos_of_ne_zero hne
        exact_mod_cast this
      rw [hST_def, ← hcast]; exact this
    have hideal : v.idealChargeDeposit shares.toRat = nav * s / ST := by
      unfold RawVault.idealChargeDeposit
      rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
    have hidpos : 0 < nav * s / ST := div_pos (mul_pos hnav_pos hshpos) hST_pos
    have hideal_nonneg : 0 ≤ v.idealChargeDeposit shares.toRat := by
      rw [hideal]; exact le_of_lt hidpos
    refine ⟨hideal_nonneg, ?_⟩
    rw [hideal]
    -- reduce the charge pipeline
    rw [if_neg hmz] at hsad
    obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    set navN := v.assetsTotal with hnavN_eq
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hc0 : c.mValue = 0
    · -- degenerate underflow: the charge is zero, overcharge is nonpositive
      have hc_zero : c.toRat = 0 := by
        rw [STAmount.toRat_signed]
        have : c.mValue.toNat = 0 := by rw [hc0]; rfl
        rw [this]; simp
      rw [hc_zero]
      have : (0 : ℚ) ≤ nav * s / ST * depositε := mul_nonneg (le_of_lt hidpos) hεnn
      linarith
    · -- genuine charge: run the relative composition
      have hQm : Q.mantissa_ ≠ 0 :=
        STAmount.ofNumber_integral_source_ne_zero v.numericType Q .upward c hint hc hc0
      have hnavnorm : navN.isNormalized := by rw [hnavN_eq]; exact v.wf.assetsTotal_norm
      obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
        STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
      have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
      rw [hshNeq] at hsnval hsnnorm
      have hshN_val : shN.toRat = s := by rw [hsnval]
      have hshN_pos : 0 < shN.toRat := by rw [hshN_val]; exact hshpos
      have hshNm : shN.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hshN_val]; exact ne_of_gt hshpos)
      have hSTnorm : v.sharesTotal.isNormalized := v.wf.sharesTotal_norm
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [← hST_def]; exact ne_of_gt hST_pos)
      have hPm : P.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
      obtain ⟨hnavm, _⟩ :=
        operator_mul_operands_ne_zero hnavnorm hsnnorm hP hPm
      obtain ⟨_, hnavbound, _, hnavN_pos⟩ :=
        Vault.depositNav_facts v navN hmz hnavm hnavN_eq
      have hPnorm : P.isNormalized :=
        operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPm
      have hQnorm : Q.isNormalized :=
        operator_div_result_isNormalized P v.sharesTotal Q .to_nearest hPnorm hSTnorm hPm hSTm hQ hQm
      -- stage bounds
      have hmulb : |P.toRat - navN.toRat * shN.toRat|
          ≤ navN.toRat * shN.toRat * (5 / (2 ^ 63 + 7)) := by
        have h : |P.toRat - navN.toRat * shN.toRat|
            ≤ |navN.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
          operator_mul_rounds_to_nearest navN shN P hnavnorm hsnnorm hP hPm
        rwa [abs_of_nonneg (by positivity : (0 : ℚ) ≤ navN.toRat * shN.toRat)] at h
      have hsubb : |navN.toRat - nav| ≤ nav * (6 / (2 ^ 63 - 3)) := hnavbound
      have hPpos : 0 < P.toRat := by
        have := abs_le.mp hmulb
        have hε : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
        nlinarith [mul_pos hnavN_pos hshN_pos]
      have hPN_pos : 0 < P.toRat / ST := div_pos hPpos hST_pos
      have hdivb : |Q.toRat - P.toRat / ST| ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) := by
        have h : |Q.toRat - P.toRat / ST| ≤ |P.toRat / ST| * (6 / (2 ^ 63 - 3)) :=
          operator_div_rounds_to_nearest P v.sharesTotal Q hPnorm hSTnorm hQ hQm
        rwa [abs_of_pos hPN_pos] at h
      have hQpos : 0 < Q.toRat := by
        have := abs_le.mp hdivb
        nlinarith
      -- h2 : the combined `sub`+`mul` numerator error
      have hnN_le : navN.toRat ≤ nav * (1 + 6 / (2 ^ 63 - 3)) := by
        have := abs_le.mp hsubb; nlinarith
      have h2 : |P.toRat - nav * s| ≤ nav * s * (12 / (2 ^ 63 - 3)) := by
        have htri : |P.toRat - nav * s|
            ≤ |P.toRat - navN.toRat * s| + |navN.toRat * s - nav * s| :=
          abs_sub_le _ _ _
        have hb1 : |P.toRat - navN.toRat * s| ≤ navN.toRat * s * (5 / (2 ^ 63 + 7)) := by
          rw [← hshN_val]; exact hmulb
        have hb2 : |navN.toRat * s - nav * s| ≤ nav * s * (6 / (2 ^ 63 - 3)) := by
          rw [show navN.toRat * s - nav * s = (navN.toRat - nav) * s from by ring, abs_mul,
            abs_of_pos hshpos]
          have := abs_le.mp hsubb
          nlinarith [hshpos]
        have hkey : navN.toRat * s * (5 / (2 ^ 63 + 7)) + nav * s * (6 / (2 ^ 63 - 3))
            ≤ nav * s * (12 / (2 ^ 63 - 3)) := by
          have he2 := charge_eps2_bound
          nlinarith [hnN_le, hshpos, hnav_pos, mul_pos hnav_pos hshpos, he2,
            mul_nonneg (le_of_lt hnav_pos) (le_of_lt hshpos)]
        linarith
      -- h3 : the division stage
      have h3 : |Q.toRat * ST - P.toRat| ≤ P.toRat * (6 / (2 ^ 63 - 3)) := by
        have hrw : Q.toRat * ST - P.toRat = (Q.toRat - P.toRat / ST) * ST := by
          field_simp
        calc |Q.toRat * ST - P.toRat|
            = |Q.toRat - P.toRat / ST| * ST := by rw [hrw, abs_mul, abs_of_pos hST_pos]
          _ ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) * ST := by
                nlinarith [hST_pos, abs_nonneg (Q.toRat - P.toRat / ST), hdivb]
          _ = P.toRat * (6 / (2 ^ 63 - 3)) := by
                rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hST_pos)]
      -- compose
      have hcomp := div_pipeline_rel_bound ST ST (nav * s) P.toRat Q.toRat 0
        (12 / (2 ^ 63 - 3)) (6 / (2 ^ 63 - 3)) depositε
        (mul_pos hnav_pos hshpos) (le_of_lt hQpos)
        (by rw [sub_self, abs_zero, mul_zero])
        h2 h3 (le_refl 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        charge_pipeline_up charge_pipeline_lo
      -- Q ≤ ideal · (1 + depositε)
      have hQ_up : Q.toRat ≤ nav * s / ST * (1 + depositε) :=
        charge_div_upper Q.toRat (nav * s) ST depositε hST_pos hcomp
      -- within one of the ceiling
      have hQneg : Q.negative_ = false := Number.negative_false_of_pos Q hQpos
      have hwithin := STAmount.ofNumber_integral_within_one v.numericType Q .upward c
        hint hQnorm hQneg hc
      have hc_le : c.toRat ≤ Q.toRat + 1 := by
        have h := (abs_lt.mp hwithin).2; linarith only [h]
      exact charge_ceiling (nav * s / ST) Q.toRat c.toRat depositε hQ_up hc_le

end XRPL.Model.SingleAssetVault
