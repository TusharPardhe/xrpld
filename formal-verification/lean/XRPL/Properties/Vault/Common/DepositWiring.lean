import XRPL.Properties.Vault.Common.RoundCanonical
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.DepositChargeProofs
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Protocol.Number.Div.Common.Decompose
import XRPL.Properties.Protocol.Number.Mul.Common.Decompose

/-! # Wiring the `Vault.deposit` accuracy headlines

Proof bodies for the deposit accuracy headlines that derive the rounded amount's
canonicity from the raw input via the `roundToVaultExponent` keystone
(`RoundCanonical.lean`) and reuse the proven exchange cores. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **The issued shares are strictly positive.** `assetsToSharesDeposit` prices a
positive canonical `amount` into a nonnegative integer count, and a nonzero result
is therefore positive. The nonnegativity walks the exact `mul`/`div` chain: the
nonzero operands come from the successful division (never a zero divisor) and the
nonzero result (never a zero numerator), so no deep-underflow floor is needed. -/
lemma assetsToSharesDeposit_pos (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hok : assetsToSharesDeposit v amount = .ok shares) (hnz : shares.isZero = false) :
    0 < shares.toRat := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  have hne0 : shares.toRat ≠ 0 := STAmount.toRat_ne_zero shares hmv
  have hamv : amount.mValue ≠ 0 := by
    intro h0
    exact absurd (show amount.toRat = 0 by rw [STAmount.toRat_signed, h0]; simp) (ne_of_gt hpos)
  suffices h : 0 ≤ shares.toRat from lt_of_le_of_ne h (Ne.symm hne0)
  unfold assetsToSharesDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: shares = ⌊normalize(amount·10^scale)⌋
    rw [if_pos hmz] at hok
    obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    have hn2m : n2.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hmv
    have hn1m : n1.mantissa_ ≠ 0 := Number.truncate_source_ne_zero n1 n2 hn2 hn2m
    have hn1cast : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).normalize largeRange.min largeRange.max
          .to_nearest = .ok n1 := hn1
    have hn1norm : n1.isNormalized :=
      normalize_result_isNormalized _ n1 .to_nearest hamv hn1cast hn1m
    have hin_nonneg : 0 ≤ (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).toRat := by
      rw [Number.toRat_of_nonneg _ rfl]; positivity
    have hround := normalize_rounds_to_nearest _ n1 hn1cast hn1m
    have hn1_nonneg : 0 ≤ n1.toRat := by
      have hb : |n1.toRat - (Number.unchecked false amount.mantissa
          (amount.exponent + (v.scale.toNat : ℤ))).toRat|
          ≤ |(Number.unchecked false amount.mantissa
          (amount.exponent + (v.scale.toNat : ℤ))).toRat| * (5 / (2 ^ 63 + 7 : ℚ)) := hround
      rw [abs_of_nonneg hin_nonneg] at hb
      have hab := abs_le.mp hb
      nlinarith [hin_nonneg]
    have hn1pos : 0 < n1.toRat :=
      lt_of_le_of_ne hn1_nonneg (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero n1 hn1m))
    obtain ⟨hn2val, hn2norm⟩ :=
      Number.truncate_floor n1 n2 hn1norm (Number.negative_false_of_pos n1 hn1pos) hn2
    have hshval : shares.toRat = n2.toRat :=
      STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide)
        (hn2norm hn2m) (by rw [hn2val]; exact Rat.den_intCast _) hsh
    rw [hshval, hn2val]
    exact_mod_cast Int.floor_nonneg.mpr hn1_nonneg
  · -- nonempty vault: shares = ⌊(sharesTotal·amount)/nav⌋
    rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
    set navN := v.assetsTotal with hnavN_eq
    obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T0, hT0, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- nonzero chain, walked backward from the nonzero result
    have hTm : T.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
    have hT0m : T0.mantissa_ ≠ 0 := Number.truncate_source_ne_zero T0 T hT hTm
    have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
    have hnavm : navN.mantissa_ ≠ 0 :=
      operator_div_divisor_ne_zero P navN T0 .to_nearest hnavnorm hT0
    have hPm : P.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz P navN T0 .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hnavm) hT0 hT0m
    obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
    have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
    rw [haneq] at hanval hannorm
    obtain ⟨hSTm, hanm⟩ :=
      operator_mul_operands_ne_zero v.wf.sharesTotal_norm hannorm hP hPm
    have hPnorm : P.isNormalized :=
      operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSTm hanm hP hPm
    have hT0norm : T0.isNormalized :=
      operator_div_result_isNormalized P navN T0 .to_nearest hPnorm hnavnorm hPm hnavm hT0 hT0m
    -- value chain: every stage is nonnegative
    have hann : 0 ≤ amountN.toRat := by rw [hanval]; exact le_of_lt hpos
    have hSTnn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
    have hPnn : 0 ≤ P.toRat := by
      have hb : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) :=
        operator_mul_rounds_to_nearest v.sharesTotal amountN P
          v.wf.sharesTotal_norm hannorm hP hPm
      rw [abs_of_nonneg (mul_nonneg hSTnn hann)] at hb
      have hab := abs_le.mp hb
      nlinarith [mul_nonneg hSTnn hann]
    obtain ⟨_, _, _, hnavpos⟩ := Vault.depositNav_facts v navN hmz hnavm hnavN_eq
    have hPNnn : 0 ≤ P.toRat / navN.toRat := div_nonneg hPnn (le_of_lt hnavpos)
    have hT0nn : 0 ≤ T0.toRat := by
      have hb : |T0.toRat - P.toRat / navN.toRat|
          ≤ |P.toRat / navN.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) :=
        operator_div_rounds_to_nearest P navN T0 hPnorm hnavnorm hT0 hT0m
      rw [abs_of_nonneg hPNnn] at hb
      have hab := abs_le.mp hb
      nlinarith [hPNnn]
    have hT0pos : 0 < T0.toRat :=
      lt_of_le_of_ne hT0nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero T0 hT0m))
    obtain ⟨hTval, hTnorm⟩ :=
      Number.truncate_floor T0 T hT0norm (Number.negative_false_of_pos T0 hT0pos) hT
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide)
        (hTnorm hTm) (by rw [hTval]; exact Rat.den_intCast _) hsh
    rw [hshval, hTval]
    exact_mod_cast Int.floor_nonneg.mpr hT0nn

/-- **The charge is stored canonically for its kind.** A nonzero
`sharesToAssetsDeposit` output is `IOUCanonical` (fractional vault) or
`IntegralCanonical` (integral vault): the empty branch canonicalizes the packed
record, and the nonempty branch packs the normalized division output through
`ofNumber`. The nonzero result forces a nonzero source, walked back to the
normalized division numerator/divisor. -/
lemma sharesToAssetsDeposit_disj_canonical (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hok : sharesToAssetsDeposit v shares = .ok c) (hc0 : c.mValue ≠ 0) :
    c.IOUCanonical ∨ c.IntegralCanonical := by
  unfold sharesToAssetsDeposit at hok
  by_cases hint : v.numericType.isIntegral = true
  · -- integral vault: both branches pack through `canonicalize`/`ofNumber` integral
    by_cases hmz : v.assetsTotal.mantissa_ = 0
    · rw [if_pos hmz] at hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      rw [STAmount.checked] at hc
      exact Or.inr (STAmount.canonicalize_integral_canonical _ c .to_nearest
        (show (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hc).1
    · rw [if_neg hmz] at hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨Q, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      exact Or.inr (STAmount.ofNumber_integral_canonical v.numericType Q .upward c hint hc).1
  · -- fractional vault: canonicalizes into `IOUCanonical`-or-zero
    have hfrac : v.numericType = .fractional := by
      cases hnt : v.numericType with
      | fractional => rfl
      | integral mv mo ms msh => rw [hnt] at hint; simp [NumericType.isIntegral] at hint
    by_cases hmz : v.assetsTotal.mantissa_ = 0
    · rw [if_pos hmz] at hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      rw [STAmount.checked] at hc
      have hcz := STAmount.canonicalize_fczr _ c .to_nearest
        (show (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).mNumericType = .fractional from hfrac) hc
      rcases hcz.2 with hio | hzero
      · exact Or.inl hio
      · exact absurd hzero hc0
    · rw [if_neg hmz] at hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      set navN := v.assetsTotal with hnavN_eq
      obtain ⟨shN, hshN, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨Q, hQ, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      have hcof : STAmount.ofNumber .fractional Q .upward = .ok c := by rw [← hfrac]; exact hc
      -- nonzero chain: c ≠ 0 forces Q ≠ 0, walked back to the pipeline operands
      have hQm : Q.mantissa_ ≠ 0 :=
        STAmount.ofNumber_iou_mantissa_ne_zero .fractional Q .upward c rfl hcof hc0
      have hApos : 0 < v.toExact.assetsTotal := by
        rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
        · exact h
        · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
      have hSTne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
        absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 := by
        refine Number.mantissa_ne_zero_of_toRat_ne_zero ?_
        rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
        exact_mod_cast hSTne
      have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
      obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
        STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
      have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
      rw [hshNeq] at hsnnorm
      have hPm : P.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
      obtain ⟨hnavm, hshNm⟩ := operator_mul_operands_ne_zero hnavnorm hsnnorm hP hPm
      have hPnorm : P.isNormalized :=
        operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPm
      have hQnorm : Q.isNormalized :=
        operator_div_result_isNormalized P v.sharesTotal Q .to_nearest hPnorm v.wf.sharesTotal_norm
          hPm hSTm hQ hQm
      obtain ⟨hlo19, hhi19⟩ := hQnorm.mantissaBounds_nat hQm
      have hQexp_lo : minExponent ≤ Q.exponent_ := by
        rcases hQnorm with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show Q.mantissa_ = 0 by rw [h0]; rfl) hQm
        · exact hlo
      rcases STAmount.ofNumber_iou_canonical_or_zero Q .upward c hlo19 hhi19 hQexp_lo hcof with hio | hzero
      · exact Or.inl hio
      · exact absurd hzero hc0

/-- `roundToVaultExponent` never changes the numeric type: the integral pass is
the identity, and the fractional pass stays fractional (the `FracCanonZero`
pipeline preserves the type). -/
lemma roundToVaultExponent_mNumericType (a : STAmount) (asset : Number) (r : STAmount)
    (hc : a.Canonical) (hok : roundToVaultExponent a asset = .ok r) :
    r.mNumericType = a.mNumericType := by
  by_cases hint : a.integral = true
  · rw [roundToVaultExponent_integral a asset hint] at hok
    rw [← Except.ok.inj hok]
  · have hfr : a.integral = false := by
      cases hb : a.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hcz : a.FracCanonZero := ⟨(hc.2 hfr).is_fractional, Or.inl (hc.2 hfr)⟩
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, _, hok⟩ := bind_ok_peel _ _ _ hok
    -- `roundToVaultExponent` is already reduced to its final direct equation.
    have hrx : a.roundToExponent postScale .downward = .ok r := hok
    rw [(STAmount.roundToExponent_fczr a r postScale .downward hcz hrx).1]
    exact hcz.1.symm

/-- **A sign-cleared `Number` source rounds to a nonnegative `ofNumber` output**
(any mode, any numeric type). Local re-derivation of the boundary fact: integral
outputs floor a nonnegative `to_rep`; fractional outputs snap a nonnegative
16-digit mantissa. -/
lemma STAmount.ofNumber_signfalse_nonneg (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) : 0 ≤ result.toRat := by
  by_cases hint : nt.isIntegral = true
  · unfold STAmount.ofNumber at hok
    simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
    cases hr : n.to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok intValue =>
      rw [hr] at hok
      simp only [] at hok
      obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n mode intValue hneg hr
      have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep intValue hnn hle
      have hres_val : result.toRat = (intValue.toInt : ℚ) := by
        have hexact := STAmount.canonicalize_integral_toRat
          (STAmount.unchecked nt intValue.toUInt64 0 false) result mode
          (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
          hval hok
        rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
        show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
        rw [toUInt64_toNat_of_nonneg intValue hnn]
      rw [hres_val]; exact_mod_cast hnn
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    by_cases hz : result.mValue = 0
    · rw [STAmount.toRat_signed, hz]; simp
    · have hn_ne : n.mantissa_ ≠ 0 :=
        STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hz
      obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
      have hexp_lo : minExponent ≤ n.exponent_ := by
        rcases hn with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
        · exact hlo
      have hok' : STAmount.ofNumber .fractional n mode = .ok result := by rw [← hnt_frac]; exact hok
      have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
        STAmount.ofNumber_iou_success_exp_range n mode result hlo19 hhi19 hexp_lo hok' hz
      obtain ⟨mant, exp, -, hval, -, hcast, -, -, -, -⟩ :=
        STAmount.ofNumber_iou_snap_pos nt n mode result hnt_frac hneg
          hlo19 hhi19 hexp_lo hexp_hi hok hz
      rw [hval, hcast]; positivity

/-- **The charge is nonnegative.** `sharesToAssetsDeposit` prices positive shares
into an asset amount, either the exact integral value (empty integral branch,
sign-cleared) or the upward `ofNumber` snap of a nonnegative division result, so it
never goes negative. The fractional empty branch (first deposit into an empty
fractional vault) needs a `canonicalize`-of-sign-cleared-source nonnegativity fact
that lacks a ready lemma; it is left as a documented gap. -/
lemma sharesToAssetsDeposit_nonneg (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    0 ≤ c.toRat := by
  unfold sharesToAssetsDeposit at hsad
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: `c = checked v.numericType shares.mantissa (shares.exponent - scale) false`
    rw [if_pos hmz] at hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hint : v.numericType.isIntegral = true
    · -- integral: `canonicalize` is value-exact on the sign-cleared, offset-0 source
      rw [STAmount.checked] at hc
      have hscale : v.scale = 0 := v.wf.scale_integral hint
      have hshexp : shares.exponent = 0 := hshc.offset_zero
      have hoff0 : (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
        show shares.exponent - (v.scale.toNat : ℤ) = 0
        rw [hshexp, hscale]; rfl
      have hval0 : (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := by
        show shares.mantissa.toNat ≤ maxRep.toNat
        have hr := hshc.in_range; rw [hshnt] at hr
        calc shares.mantissa.toNat ≤ NumericType.int64.maxValue.toNat := hr
          _ = maxRep.toNat := by decide
      have hcval := STAmount.canonicalize_integral_toRat _ c .to_nearest
        (show (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff0 hval0 hc
      rw [hcval, STAmount.toRat_of_nonneg _ rfl]; positivity
    · -- fractional empty vault: `checked = canonicalize (unchecked ... false)`, and the
      -- sign-cleared source stays nonnegative through the `iou`/`normalize` snap.
      have hnt_frac : v.numericType = .fractional := by
        cases hnt2 : v.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt2] at hint; exact absurd rfl hint
      have hsh_hi : shares.mValue.toNat < 2 ^ 63 := by
        have hr : shares.mValue.toNat ≤ maxRep.toNat := by
          have h := hshc.in_range; rw [hshnt] at h
          calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := h
            _ = maxRep.toNat := by decide
        have hmr : maxRep.toNat = 9223372036854775807 := by decide
        omega
      rw [STAmount.checked] at hc
      exact STAmount.canonicalize_signfalse_nonneg
        (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false)
        c .to_nearest hnt_frac rfl hsh_hi hc
  · -- nonempty vault: `c = ofNumber v.numericType Q .upward` with `Q ≥ 0`. The
    -- positive, normalized `Q` is read off the `sub`/`mul`/`div` pipeline exactly as
    -- in `sharesToAssetsDeposit_charge_integral_bound` (nav > 0, shares > 0 give
    -- `P, Q > 0`), and `ofNumber_signfalse_nonneg` then yields `0 ≤ c.toRat`.
    -- Reusing that pipeline walk here is the remaining step.
    rw [if_neg hmz] at hsad
    obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
    set navN := v.assetsTotal with hnavN_eq
    obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hc0 : c.mValue = 0
    · rw [STAmount.toRat_signed, show c.mValue.toNat = 0 from by rw [hc0]; rfl]; simp
    · -- `Q` is positive and normalized; the upward `ofNumber` snap is nonnegative
      have hApos : 0 < v.toExact.assetsTotal := by
        rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
        · exact h
        · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
      have hST_pos : 0 < v.sharesTotal.toRat := by
        have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
          absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
        have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
        rw [← hcast]; exact_mod_cast Nat.pos_of_ne_zero hne
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hST_pos)
      have hQm : Q.mantissa_ ≠ 0 := by
        by_cases hint : v.numericType.isIntegral = true
        · exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .upward c hint hc hc0
        · have hfrac : v.numericType = .fractional := by
            cases hnt : v.numericType with
            | fractional => rfl
            | integral mv mo ms msh => rw [hnt] at hint; simp [NumericType.isIntegral] at hint
          exact STAmount.ofNumber_iou_mantissa_ne_zero v.numericType Q .upward c hfrac hc hc0
      have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
      obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
        STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
      have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
      rw [hshNeq] at hsnval hsnnorm
      have hshN_pos : 0 < shN.toRat := by rw [hsnval]; exact hshpos
      have hshNm : shN.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hshN_pos)
      have hPm : P.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
      obtain ⟨hnavm, _⟩ := operator_mul_operands_ne_zero hnavnorm hsnnorm hP hPm
      obtain ⟨_, _, _, hnavN_pos⟩ := Vault.depositNav_facts v navN hmz hnavm hnavN_eq
      have hPnorm : P.isNormalized :=
        operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPm
      have hQnorm : Q.isNormalized :=
        operator_div_result_isNormalized P v.sharesTotal Q .to_nearest hPnorm v.wf.sharesTotal_norm
          hPm hSTm hQ hQm
      have hmulb : |P.toRat - navN.toRat * shN.toRat|
          ≤ navN.toRat * shN.toRat * (5 / (2 ^ 63 + 7)) := by
        have h : |P.toRat - navN.toRat * shN.toRat|
            ≤ |navN.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
          operator_mul_rounds_to_nearest navN shN P hnavnorm hsnnorm hP hPm
        rwa [abs_of_nonneg (by positivity : (0 : ℚ) ≤ navN.toRat * shN.toRat)] at h
      have hPpos : 0 < P.toRat := by
        have := abs_le.mp hmulb
        nlinarith [mul_pos hnavN_pos hshN_pos]
      have hPN_pos : 0 < P.toRat / v.sharesTotal.toRat := div_pos hPpos hST_pos
      have hdivb : |Q.toRat - P.toRat / v.sharesTotal.toRat|
          ≤ P.toRat / v.sharesTotal.toRat * (6 / (2 ^ 63 - 3)) := by
        have h : |Q.toRat - P.toRat / v.sharesTotal.toRat|
            ≤ |P.toRat / v.sharesTotal.toRat| * (6 / (2 ^ 63 - 3)) :=
          operator_div_rounds_to_nearest P v.sharesTotal Q hPnorm v.wf.sharesTotal_norm hQ hQm
        rwa [abs_of_pos hPN_pos] at h
      have hQpos : 0 < Q.toRat := by
        have := abs_le.mp hdivb
        nlinarith
      have hQneg : Q.negative_ = false := Number.negative_false_of_pos Q hQpos
      exact STAmount.ofNumber_signfalse_nonneg v.numericType Q .upward c hQnorm hQneg hc


/-- Proof body of `Vault.deposit_charge_integral`. The rounded amount equals the
integral input (identity pass), the issued shares are a positive `int64` count,
and the proven `sharesToAssetsDeposit_charge_integral_bound` bounds the overcharge. -/
theorem Vault.deposit_charge_integral_proof (v : Vault) (amountDeposit : STAmount)
    (r : DepositResult) (hcanon : amountDeposit.Canonical)
    (hint : v.numericType.isIntegral = true) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      1 + v.idealChargeDeposit r.sharesIssued.toRat * depositε := by
  obtain ⟨amount, rawAssetDeposited, assetDeposited, sh, cN, sN, at', av', st', hround, hanz, _, _, _, hcd,
    _, _, _, _, _, _, hamt, hshr, _⟩ :=
    Vault.deposit_success_reduces v amountDeposit false r hok herr
  obtain ⟨shares, hats, hsz, hsad, hgt, hsheq⟩ :=
    computeDeposit_success_reduces v amount rawAssetDeposited sh (hcd rfl).1
  -- Exchange facts belong to the raw `computeDeposit` charge.
  have hcty : rawAssetDeposited.mNumericType = v.numericType :=
    (sharesToAssetsDeposit_integral_canonical v shares rawAssetDeposited hint hsad).2
  have hcmp : STAmount.areComparable amount rawAssetDeposited = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; simpa using hcond
  have hamt_int : amount.integral = true := by
    have htyeq : amount.mNumericType = rawAssetDeposited.mNumericType := by
      have := hcmp; unfold STAmount.areComparable at this
      exact beq_iff_eq.mp this
    unfold STAmount.integral; rw [htyeq, hcty]; exact hint
  -- so the input is integral, `roundToVaultExponent` was the identity
  have hameq : amount = amountDeposit := by
    have htype := roundToVaultExponent_mNumericType amountDeposit v.assetsTotal amount hcanon hround
    have hadint : amountDeposit.integral = true := by
      unfold STAmount.integral at hamt_int ⊢; rw [← htype]; exact hamt_int
    rw [roundToVaultExponent_integral amountDeposit v.assetsTotal hadint] at hround
    exact (Except.ok.inj hround).symm
  rw [hameq] at hats
  -- issued shares: positive `int64` canonical count
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amountDeposit shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v amountDeposit shares hcanon hpos hats hsz
  have hraw_nonneg : 0 ≤ rawAssetDeposited.toRat :=
    sharesToAssetsDeposit_nonneg v shares rawAssetDeposited hshc hshnt hshpos hsad
  -- The integral clamp returns the raw amount or its absolute form. The raw
  -- exchange charge is nonnegative, so the final state amount has the same value
  -- without asserting record identity.
  have hfinal_raw : assetDeposited.toRat = rawAssetDeposited.toRat := by
    have hraw_int : rawAssetDeposited.integral = true :=
      (sharesToAssetsDeposit_integral_canonical v shares rawAssetDeposited hint hsad).1.is_integral
    have hclamp := (hcd rfl).2.1
    unfold clampToSumExponent at hclamp
    rw [if_pos hraw_int] at hclamp
    by_cases hneg : rawAssetDeposited.negative = true
    · rw [if_pos hneg] at hclamp
      have hfinal : assetDeposited = rawAssetDeposited.operator_neg :=
        (Except.ok.inj hclamp).symm
      rw [hfinal, STAmount.operator_neg_toRat]
      have hraw_nonpos : rawAssetDeposited.toRat ≤ 0 :=
        STAmount.toRat_nonpos_of rawAssetDeposited hneg
      linarith
    · rw [if_neg hneg] at hclamp
      exact Except.ok.inj hclamp |>.symm ▸ rfl
  -- Apply the proven raw-charge bound, then transport it to the final state amount.
  obtain ⟨_, hbound⟩ :=
    sharesToAssetsDeposit_charge_integral_bound v amountDeposit shares rawAssetDeposited hint hshc hshnt hshpos hsad
  have hcr : r.amountDeposit' = assetDeposited := hamt
  have hsr : r.sharesIssued = shares := by rw [hshr, hsheq]
  rw [hcr, hsr, hfinal_raw]
  exact hbound

/-- The charge type matches the vault's numeric type: both packings route through
`checked`/`ofNumber` on `vault.numericType`, which preserve the type. -/
lemma sharesToAssetsDeposit_mNumericType (v : Vault) (shares c : STAmount)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.mNumericType = v.numericType := by
  unfold sharesToAssetsDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq, STAmount.checked] at hcx
    exact STAmount.canonicalize_mNumericType _ c .to_nearest hcx
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨Q, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hcx
    exact STAmount.ofNumber_mNumericType v.numericType Q .upward c hcx

/-- **The integral charge fits `maxRep`.** On an integral vault the packing routes
through `checked`/`ofNumber`, whose stored magnitude never exceeds `maxRep`. -/
lemma sharesToAssetsDeposit_le_maxRep (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hint : v.numericType.isIntegral = true)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.mValue.toNat ≤ maxRep.toNat := by
  have hscale0 : v.scale = 0 := v.wf.scale_integral hint
  unfold sharesToAssetsDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq, STAmount.checked] at hcx
    have hoff : (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
      show shares.mOffset - (v.scale.toNat : ℤ) = 0
      rw [hshc.offset_zero, hscale0]; simp
    have hval : (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := by
      show shares.mValue.toNat ≤ maxRep.toNat
      have hr := hshc.in_range; rw [hshnt] at hr
      calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
        _ = maxRep.toNat := by decide
    obtain ⟨_, _, hle, _⟩ := STAmount.canonicalize_integral_facts _ c .to_nearest
      (show (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff hval hcx
    exact hle
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨Q, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hcx
    obtain ⟨_, _, hle⟩ := STAmount.ofNumber_integral_facts v.numericType Q .upward c hint hcx
    exact hle

/-- **The charge is `ExactCanonical` or zero.** A nonzero charge is canonical for
its kind (`sharesToAssetsDeposit_disj_canonical`); the integral kind additionally
fits `Int64` because its type equals the vault's, which is integral. -/
lemma sharesToAssetsDeposit_exactCanonical_or_zero (v : Vault)
    (shares c : STAmount) (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.ExactCanonical ∨ c.mValue = 0 := by
  by_cases hc0 : c.mValue = 0
  · exact Or.inr hc0
  refine Or.inl ?_
  rcases sharesToAssetsDeposit_disj_canonical v shares c hshc hshnt hok hc0 with hio | hic
  · exact Or.inl hio
  · have htyeq : c.mNumericType = v.numericType :=
      sharesToAssetsDeposit_mNumericType v shares c hok
    have hint : v.numericType.isIntegral = true := by rw [← htyeq]; exact hic.is_integral
    refine Or.inr ⟨hic, ?_⟩
    have hle := sharesToAssetsDeposit_le_maxRep v shares c hshc hshnt hint hok
    calc c.mValue.toNat ≤ maxRep.toNat := hle
      _ ≤ 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num

/-- **The charge converts exactly through `toNumber`.** The taken amount is stored
canonically for its kind (or is a fractional zero, handled by
`toNumber_zero_fractional`), so its `to_nearest` `Number` conversion is value-exact
and normalized. -/
lemma sharesToAssetsDeposit_toNumber_exact (v : Vault) (shares a : STAmount)
    (cN : Number) (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hsad : sharesToAssetsDeposit v shares = .ok a)
    (hcN : a.toNumber .to_nearest = .ok cN) :
    cN.toRat = a.toRat ∧ cN.isNormalized := by
  rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares a hshc hshnt hsad with hexact | ha0
  · obtain ⟨an, han, hval, hnorm⟩ := STAmount.toNumber_exact_canonical a .to_nearest hexact
    have hcNeq : an = cN := by rw [han] at hcN; exact Except.ok.inj hcN
    rw [← hcNeq]; exact ⟨hval, hnorm⟩
  · by_cases haint : a.integral = true
    · have htyeq := sharesToAssetsDeposit_mNumericType v shares a hsad
      have hvint : v.numericType.isIntegral = true := by
        show v.numericType.isIntegral = true
        rw [← htyeq]; exact haint
      obtain ⟨hIC, _⟩ := sharesToAssetsDeposit_integral_canonical v shares a hvint hsad
      have hexact : a.ExactCanonical := Or.inr ⟨hIC, by rw [ha0]; exact Nat.zero_le _⟩
      obtain ⟨an, han, hval, hnorm⟩ := STAmount.toNumber_exact_canonical a .to_nearest hexact
      have hcNeq : an = cN := by rw [han] at hcN; exact Except.ok.inj hcN
      rw [← hcNeq]; exact ⟨hval, hnorm⟩
    · have hafr : a.integral = false := by
        cases hb : a.integral with
        | false => rfl
        | true => exact absurd hb haint
      have hczero := STAmount.toNumber_zero_fractional a .to_nearest hafr ha0
      have hcNeq : cN = Number.zero := by rw [hczero] at hcN; exact (Except.ok.inj hcN).symm
      subst hcNeq
      refine ⟨?_, Or.inl rfl⟩
      rw [Number.toRat_zero, STAmount.toRat_signed, ha0]; simp

/-- **The `assetsMaximum` guard never fires when the exact sum stays under the
maximum.** The stored total rounds `assetsTotal + charge` to nearest, and a
normalized maximum the exact sum is under is never crossed by the rounding, so the
`operator_gt` guard reads `false`. -/
lemma deposit_maximum_guard_false (v : Vault) (cN at' : Number)
    (hcNnorm : cN.isNormalized)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hbound : ∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat + cN.toRat ≤ m.toRat) :
    ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false := by
  have hatnorm : at'.isNormalized := by
    by_cases h0 : at'.mantissa_ = 0
    · rw [Number.operator_add_zero_shape_sz v.assetsTotal cN at' v.wf.assetsTotal_norm hcNnorm hat h0]
      exact Or.inl rfl
    · exact operator_add_isNormalized_to_nearest v.assetsTotal cN at'
        v.wf.assetsTotal_norm hcNnorm hat h0
  cases hm : v.assetsMaximum with
  | none =>
    simp only [Option.getD_none]
    rw [show Number.zero.operator_ne Number.zero = false from by decide, Bool.false_and]
  | some m =>
    have hmem : m ∈ v.assetsMaximum := by rw [hm]; exact Option.mem_some_self m
    have hmnorm : m.isNormalized := v.wf.assetsMaximum_norm m hmem
    have hle : v.assetsTotal.toRat + cN.toRat ≤ m.toRat := hbound m hmem
    have hat_le : at'.toRat ≤ m.toRat :=
      operator_add_le_of_le_normalized v.assetsTotal cN at' m v.wf.assetsTotal_norm hcNnorm hat hmnorm hle
    have hgt_false : at'.operator_gt m = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      have := (operator_gt_iff at' m hatnorm hmnorm).mp h
      linarith
    simp only [Option.getD_some]
    rw [hgt_false, Bool.and_false]

/-- **Charge-side bound for the limit guard.** On a real deposit the charge's
`Number` never pushes `assetsTotal + charge` over a maximum the rounded deposit
already fits under: a genuine charge is at most the rounded amount, and an
underflowed (zero) charge leaves the total at `assetsTotal`, which a lawful vault
keeps under its own maximum. -/
lemma deposit_real_charge_bound (v : Vault)
    (amount roundedAmount a sh : STAmount) (cN : Number)
    (hcanonR : roundedAmount.Canonical) (hnzR : roundedAmount.isZero = false)
    (hameq : amount = roundedAmount)
    (hcd : computeDeposit v amount = .ok (.success a sh))
    (hcN : a.toNumber .to_nearest = .ok cN)
    (hmargin : ∀ m ∈ v.assetsMaximum, v.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat) :
    ∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat + cN.toRat ≤ m.toRat := by
  intro m hm
  obtain ⟨shares, hats, hshz, hsad, hgt, hseq⟩ := computeDeposit_success_reduces v amount a sh hcd
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hats
  obtain ⟨hcNval, hcNnorm⟩ :=
    sharesToAssetsDeposit_toNumber_exact v shares a cN hshc hshnt hsad hcN
  have hcmp_ba : STAmount.areComparable amount a = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; simpa using hcond
  have hcmp_ab : STAmount.areComparable a amount = true := by
    rw [STAmount.areComparable_comm]; exact hcmp_ba
  have hAeq : v.assetsTotal.toRat = v.toExact.assetsTotal := rfl
  by_cases ha0 : a.mValue = 0
  · have haR0 : a.toRat = 0 := (STAmount.toRat_eq_zero_iff a).mpr ha0
    have hcapm : v.toExact.assetsTotal ≤ m.toRat :=
      v.exact.cap m.toRat (Option.mem_map_of_mem _ hm)
    rw [hcNval, haR0, hAeq]; linarith
  · have hexact : a.ExactCanonical := by
      rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares a hshc hshnt hsad with h | h0
      · exact h
      · exact absurd h0 ha0
    have hexactAmt : amount.ExactCanonical := by
      rw [hameq]; exact STAmount.Canonical.exactCanonical roundedAmount hcanonR
    have hamt0 : amount.mValue ≠ 0 := by
      rw [hameq]; intro h; rw [STAmount.isZero, h] at hnzR; simp at hnzR
    have hcmpF : STAmount.CmpFaithful a amount :=
      STAmount.CmpFaithful.ofExactCanonical a amount hexact hexactAmt hcmp_ab
        (fun h => absurd h ha0) (fun h => absurd h hamt0)
    have hcharge_le : a.toRat ≤ amount.toRat :=
      computeDeposit_success_charge_le v amount a sh hcmpF hcd
    rw [hameq] at hcharge_le
    rw [hcNval, hAeq]
    have := hmargin m hm
    linarith

/-- Proof body of `Vault.deposit_under_maximum`. -/
theorem Vault.deposit_under_maximum_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hcanon : amountDeposit.Canonical)
    (hok : v.deposit amountDeposit isDonation = .ok r)
    (hmargin : ∀ m ∈ v.assetsMaximum,
      v.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat)
    (hfinalMax : ∀ (rawAssetDeposited assetDeposited sharesCreated : STAmount) (cN at' : Number),
      computeDeposit v roundedAmount = .ok (.success rawAssetDeposited sharesCreated) →
      clampToSumExponent v.assetsTotal rawAssetDeposited = .ok assetDeposited →
      assetDeposited.isFractionalNonPositive = .ok false →
      assetDeposited.toNumber .to_nearest = .ok cN →
      v.assetsTotal.operator_add cN .to_nearest = .ok at' →
      ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
        at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false) :
    r.error ≠ some .tecLIMIT_EXCEEDED := by
  intro hLE
  obtain ⟨hround0, hnzR⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hcanonR : roundedAmount.Canonical :=
    Vault.roundedDepositAmount_canonical v amountDeposit roundedAmount hcanon hrounded
  unfold Vault.deposit at hok
  simp only [] at hok
  obtain ⟨amount, hround, hok⟩ := bind_ok_peel _ _ _ hok
  have hameq : amount = roundedAmount := Except.ok.inj (hround.symm.trans hround0)
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · rw [if_neg (by simp [hd])] at hok
          obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨sN, hsN, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
          · have hcanon_amt : amount.Canonical := by rw [hameq]; exact hcanonR
            obtain ⟨an, han, hval, hnorm⟩ := STAmount.toNumber_exact_canonical amount .to_nearest
              (STAmount.Canonical.exactCanonical amount hcanon_amt)
            have hn1eq : an = n1 := by rw [han] at hn1; exact Except.ok.inj hn1
            rw [hn1eq] at hval hnorm
            have hbound : ∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat + n1.toRat ≤ m.toRat := by
              intro m hm2
              rw [hval, hameq]
              have hmarg := hmargin m hm2
              have hAeq : v.assetsTotal.toRat = v.toExact.assetsTotal := rfl
              linarith
            have hgf := deposit_maximum_guard_false v n1 at' hnorm hat hbound
            rw [hgf] at hm; exact absurd hm (by simp)
          · rw [if_neg hm] at hok
            obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp)
        · rw [if_pos (by simpa using hd)] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          rcases computeDeposit_codes v amount cres hcd with h5 | h5 | h5 | ⟨a, sh, h5⟩
          · subst h5; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
          · subst h5; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
          · subst h5; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
          · subst h5
            simp only [] at hok
            obtain ⟨assetDeposited, hclamp, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨nonpositive, hprecision, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hnp : nonpositive = true
            · rw [if_pos hnp] at hok
              injection hok with h; rw [← h] at hLE
              exact absurd hLE (by simp [DepositResult.rejected])
            · rw [if_neg hnp] at hok
              obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨sN, hsN, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
              by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
              · have hprecisionFalse : assetDeposited.isFractionalNonPositive = .ok false := by
                  rw [hprecision]
                  simpa using hnp
                have hcdR : computeDeposit v roundedAmount = .ok (.success a sh) := by
                  rw [← hameq]
                  exact hcd
                have hgf := hfinalMax a assetDeposited sh n1 at' hcdR hclamp hprecisionFalse hn1 hat
                rw [hgf] at hm; exact absurd hm (by simp)
              · rw [if_neg hm] at hok
                obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
                injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp)

/-- The `int64` zero amount reduces to the canonical record `⟨.int64, 0, 0, false⟩`. -/
lemma STAmount.zero_int64_eq : STAmount.zero .int64 = ⟨.int64, 0, 0, false⟩ := by decide

/-- The `int64` zero amount is `IntegralCanonical`. -/
lemma zero_int64_IntegralCanonical : (STAmount.zero .int64).IntegralCanonical := by
  rw [STAmount.zero_int64_eq]; exact ⟨by decide, by decide, by decide⟩

/-- The `int64` zero amount has zero exact value. -/
lemma STAmount.zero_int64_toRat : (STAmount.zero .int64).toRat = 0 := by
  rw [STAmount.zero_int64_eq, STAmount.toRat_signed]; norm_num

/-- The `int64` zero amount carries the `int64` numeric type. -/
lemma STAmount.zero_int64_mNumericType : (STAmount.zero .int64).mNumericType = .int64 := by
  rw [STAmount.zero_int64_eq]

/-- Proof body of `Vault.deposit_vault_updates`. Both stored asset totals round
`old + taken` within `depositε` (the taken amount is nonnegative, so the `Number`
addition never cancels), and the share total is stored exactly whenever the sum
fits the `int64` domain. -/
theorem Vault.deposit_vault_updates_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (hcanon : amountDeposit.Canonical)
    (hpos : 0 < amountDeposit.toRat) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) (herr : r.error = none) :
    ∃ cN : Number,
      r.amountDeposit'.toNumber .to_nearest = .ok cN ∧
      v.assetsTotal.operator_add cN .to_nearest = .ok r.vault'.assetsTotal ∧
      v.assetsAvailable.operator_add cN .to_nearest = .ok r.vault'.assetsAvailable ∧
      ∃ sN : Number,
        r.sharesIssued.toNumber .to_nearest = .ok sN ∧
        v.sharesTotal.operator_add sN .to_nearest = .ok r.vault'.sharesTotal := by
  obtain ⟨am, rawAssetDeposited, assetDeposited, sharesCreated, cN, sN, at', av', st',
    hround, hamz, hsh_don, hins, hdon_eq, hcomp, hcN, hsN, hat, hav, hst, hmax,
    hamt, hshr, hrv⟩ :=
    Vault.deposit_success_reduces v amountDeposit isDonation r hok herr
  refine ⟨cN, ?_, ?_, ?_, sN, ?_, ?_⟩
  · rw [hamt]; exact hcN
  · rw [hrv]; exact hat
  · rw [hrv]; exact hav
  · rw [hshr]; exact hsN
  · rw [hrv]; exact hst

end XRPL.Model.SingleAssetVault
