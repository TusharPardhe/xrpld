import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.ExchangeShared
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact

/-! # Fractional-upward charge core for `Vault.deposit`

The fractional charge `sharesToAssetsDeposit` prices the issued shares back into a
fractional asset by an upward `ofNumber` snap of the `sub`/`mul`/`div` pipeline
result `Q`. Unlike the integral packing (which snaps to a whole unit, overshooting
by at most `1`), the fractional packing snaps onto the `10^exponent` grid, so it
overshoots `Q` by at most one ULP `10^result.exponent`.

This is the fractional counterpart of `STAmount.ofNumber_integral_within_one` used
by the integral charge bound. It reads the ceiling directly off the two-sided ULP
bound `ofNumber_iou_within_ulp`, whose gap `10^(r.exponent_+3)` is dominated by the
result ULP `10^result.exponent` (the snap never lowers the exponent below
`r.exponent_+3`). -/

namespace XRPL.Model.Protocol

/-- **Fractional upward `ofNumber` ceiling.** A fractional upward snap of a
19-digit-normalized nonnegative `Number` `r` overshoots by at most one ULP of the
stored result: `result.toRat ≤ r.toRat + 10^result.exponent`. The two-sided ULP
bound already caps `result.toRat - r.toRat` by `10^(r.exponent_+3)`, and the snap
keeps `r.exponent_+3 ≤ result.exponent`, so that gap is at most the result ULP. -/
lemma STAmount.ofNumber_upward_ceiling_bounds (nt : NumericType) (r : Number)
    (result : STAmount)
    (hnt : nt = .fractional)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r .upward = .ok result) (hresult : result.mValue ≠ 0) :
    result.toRat ≤ r.toRat + (10 : ℚ) ^ result.exponent := by
  obtain ⟨hulp, hexp⟩ := STAmount.ofNumber_iou_within_ulp nt r .upward result hnt
    hr_lo hr_hi hre_lo hre_hi hok hresult
  have hgap : result.toRat - r.toRat ≤ (10 : ℚ) ^ (r.exponent_ + 3) := (abs_le.mp hulp).2
  have hdom : (10 : ℚ) ^ (r.exponent_ + 3) ≤ (10 : ℚ) ^ result.exponent :=
    zpow_le_zpow_right₀ (by norm_num) hexp
  linarith

/-- **Fractional upward `ofNumber` floor.** A fractional upward snap of a
19-digit-normalized nonnegative `Number` `r` never lowers the value:
`r.toRat ≤ result.toRat`. The upward 16-digit re-round is the exact ceiling
`⌈M/1000⌉·10^(e+3)` at scale `e+3`, which sits at or above `M·10^e = r.toRat`. -/
lemma STAmount.ofNumber_upward_floor_bounds (nt : NumericType) (r : Number)
    (result : STAmount)
    (hnt : nt = .fractional) (hr_neg : r.negative_ = false)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r .upward = .ok result) (hresult : result.mValue ≠ 0) :
    r.toRat ≤ result.toRat := by
  obtain ⟨mant, exp, hnorm, hres_toRat, -, -, -, -, -, -⟩ :=
    STAmount.ofNumber_iou_snap_pos nt r .upward result hnt hr_neg hr_lo hr_hi hre_lo hre_hi hok hresult
  obtain ⟨hceil, -⟩ :=
    normalizeToRange_16_ceil_pos r mant exp hr_neg hr_lo hr_hi (by omega) hre_hi hnorm
  rw [hres_toRat, hceil, Number.toRat_of_nonneg r hr_neg]
  -- `M·10^e ≤ ⌈M/1000⌉·10^(e+3) = (⌈M/1000⌉·1000)·10^e`, using `M ≤ ⌈M/1000⌉·1000`.
  have hpow : (10 : ℚ) ^ (r.exponent_ + 3) = (10 : ℚ) ^ r.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
  have hnat : r.mantissa_.toNat
      ≤ (r.mantissa_.toNat / 1000 + (if r.mantissa_.toNat % 1000 ≠ 0 then 1 else 0)) * 1000 := by
    by_cases hrem : r.mantissa_.toNat % 1000 = 0
    · rw [if_neg (by omega)]; omega
    · rw [if_pos hrem]; omega
  have hnatq : (r.mantissa_.toNat : ℚ)
      ≤ ((r.mantissa_.toNat / 1000 + (if r.mantissa_.toNat % 1000 ≠ 0 then 1 else 0) : ℕ) : ℚ)
        * 1000 := by
    have := (Nat.cast_le (α := ℚ)).mpr hnat
    push_cast at this ⊢; linarith
  have hpe_pos : (0 : ℚ) < (10 : ℚ) ^ r.exponent_ := zpow_pos (by norm_num) _
  rw [hpow]
  calc (r.mantissa_.toNat : ℚ) * (10 : ℚ) ^ r.exponent_
      ≤ (((r.mantissa_.toNat / 1000 + (if r.mantissa_.toNat % 1000 ≠ 0 then 1 else 0) : ℕ) : ℚ) * 1000)
          * (10 : ℚ) ^ r.exponent_ := by
        exact mul_le_mul_of_nonneg_right hnatq (le_of_lt hpe_pos)
    _ = ((r.mantissa_.toNat / 1000 + (if r.mantissa_.toNat % 1000 ≠ 0 then 1 else 0) : ℕ) : ℚ)
          * ((10 : ℚ) ^ r.exponent_ * 1000) := by ring

/-- **`.upward` `to_rep` on a sign-cleared `Number` is the integer ceiling.**
When `sbit_ = false` the `.upward` round decision bumps by one exactly when the
shifted-off fraction is nonzero, so the stored integer sits at or above the value:
`n.toRat ≤ r.toInt`. Directed companion of `to_rep_downward_floor`; feeds the
integral charge's lower `depositε` band (the taken amount never dips below the
issued shares' worth). -/
lemma Number.to_rep_upward_ceil (n : Number) (r : Int64)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : n.to_rep .upward = .ok r) :
    n.toRat ≤ (r.toInt : ℚ) := by
  by_cases hexp0 : 0 ≤ n.exponent
  · exact le_of_eq (to_rep_exact_of_exponent_nonneg n .upward r hn hexp0 hok).symm
  · push_neg at hexp0
    unfold Number.to_rep at hok
    simp only at hok
    by_cases hz : (n.mantissa == 0) = true
    · rw [if_pos hz] at hok
      have hr : r = 0 := by injection hok with h; exact h.symm
      have hmant0 : n.mantissa.toInt = 0 := by rw [beq_iff_eq] at hz; rw [hz]; decide
      have htr : n.toRat = 0 := by rw [← mantissa_mul_exponent_eq_toRat n hn, hmant0]; norm_num
      rw [hr, htr, show (0 : Int64).toInt = 0 from by decide]; norm_num
    · rw [if_neg hz] at hok
      have hmag_nn : 0 ≤ n.mantissa.toInt := (mantissa_sign n).2 hneg
      have hmagM_le : n.mantissa.toInt.natAbs ≤ maxRep.toNat := mantissa_natAbs_le_maxRep n hn
      rw [hneg] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_pos hexp0, if_neg (by omega : ¬ n.exponent ≥ 0)] at hok
      simp only at hok
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      set k : ℕ := (-n.exponent).toNat with hkdef
      have hk_pos : 1 ≤ k := by rw [hkdef]; omega
      have hk_cast : (k : ℤ) = -n.exponent := by rw [hkdef]; omega
      have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ k := by
        rw [hspdef]; exact shift_fst_eq n.mantissa n.exponent Guard.new hmag_nn
      have hsp_nn : 0 ≤ sp.1.toInt := by rw [hDf]; exact Int.ediv_nonneg hmag_nn (by positivity)
      have hval : n.toRat = (n.mantissa.toInt : ℚ) * (10 : ℚ) ^ n.exponent :=
        (mantissa_mul_exponent_eq_toRat n hn).symm
      have hexp_pow : (10 : ℚ) ^ n.exponent = ((10 : ℚ) ^ k)⁻¹ := by
        rw [show n.exponent = -(k : ℤ) from by omega, zpow_neg, zpow_natCast]
      set frac : ℚ := ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) / 10 ^ k with hfrac_def
      have h10k_pos : (0 : ℚ) < 10 ^ k := by positivity
      have hd_q : (n.mantissa.toInt : ℚ)
          = 10 ^ k * ((n.mantissa.toInt / 10 ^ k : ℤ) : ℚ) + ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) := by
        exact_mod_cast (Int.mul_ediv_add_emod n.mantissa.toInt (10 ^ k)).symm
      have hval_frac : n.toRat = (sp.1.toInt : ℚ) + frac := by
        have key : (n.mantissa.toInt : ℚ)
            = (sp.1.toInt : ℚ) * 10 ^ k + ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) := by
          rw [hDf]; linear_combination hd_q
        rw [hval, hexp_pow, ← div_eq_mul_inv, hfrac_def, key]; field_simp
      have hfrac_nn : 0 ≤ frac := by
        rw [hfrac_def]; apply div_nonneg _ (le_of_lt h10k_pos)
        exact_mod_cast Int.emod_nonneg _ (by positivity)
      have hfrac_lt : frac < 1 := by
        rw [hfrac_def, div_lt_one h10k_pos]
        exact_mod_cast Int.emod_lt_of_pos _ (by positivity)
      have hrep : represents sp.2 frac := by
        have := Number.to_rep_shift_represents n.mantissa n.exponent Guard.new hmag_nn 0 represents_new
        rw [← hspdef, ← hkdef] at this
        simpa [hfrac_def] using this
      have hsp_lt : sp.1.toUInt64.toNat < maxRep.toNat := by
        have h2 : n.mantissa.toInt ≤ (maxRep.toNat : ℤ) := by omega
        have hsp_lt_int : sp.1.toInt < (maxRep.toNat : ℤ) := by
          by_contra hcon
          push_neg at hcon
          have hmul_le : sp.1.toInt * 10 ^ k ≤ n.mantissa.toInt := by
            rw [hDf]; exact Int.ediv_mul_le _ (by positivity)
          have h10k_ge : (10 : ℤ) ≤ 10 ^ k := by
            calc (10 : ℤ) = 10 ^ 1 := by norm_num
              _ ≤ 10 ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
          have hmr : (1 : ℤ) ≤ maxRep.toNat := by decide
          nlinarith [hmul_le, h2, hcon, h10k_ge, hmr,
            mul_le_mul_of_nonneg_right hcon (show (0 : ℤ) ≤ 10 ^ k from by positivity),
            mul_le_mul_of_nonneg_left h10k_ge (show (0 : ℤ) ≤ (maxRep.toNat : ℤ) from by positivity)]
        have hnat : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
        omega
      have hpof : sp.2.pushOverflow sp.1.toUInt64 .upward = sp.2 :=
        pushOverflow_noop_of_lt_maxRep hsp_lt sp.2 .upward
      rw [hpof] at hok
      have hno_cusp : ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) := fun hc => by
        have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
        have hnat : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
        omega
      have hsbit : sp.2.sbit_ = false := by
        rw [hspdef, Number.to_rep_shift_sbit n.mantissa n.exponent Guard.new]; rfl
      by_cases hb : (sp.2.round .upward == 1 || (sp.2.round .upward == 0 && sp.1 % 2 == 1)) = true
      · -- the fraction bumps `sp.1` up to the ceiling `sp.1 + 1`
        rw [if_pos hb] at hok
        by_cases hovf : sp.1 ≥ maxRep.toInt64
        · rw [if_pos hovf] at hok; exact absurd hok (by simp)
        · rw [if_neg hovf] at hok
          have hovf' : sp.1.toInt < (maxRep.toNat : ℤ) := by
            have hnat : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
            omega
          clear hovf
          have hadd : (sp.1 + 1).toInt = sp.1.toInt + 1 := by
            rw [Int64.toInt_add, int64_one_toInt, Int.bmod_eq_iff (by norm_num)]
            rw [maxRep_val] at hovf'; refine ⟨by omega, by push_cast; omega⟩
          have hr : r = sp.1 + 1 := by injection hok with h; exact h.symm
          rw [hr, hadd, hval_frac]; push_cast; linarith
      · -- no bump: the `.upward` decision was not `1`, so the guard is empty and the
        -- shifted-off fraction is zero, hence the value is the exact integer `sp.1`
        rw [if_neg hb, if_neg hno_cusp] at hok
        have hr : r = sp.1 := by injection hok with h; exact h.symm
        have hemp : sp.2.empty = true := by
          by_contra hcon
          have hne' : sp.2.empty = false := by simpa using hcon
          apply hb
          have hrv1 : sp.2.round .upward = 1 := by
            unfold Guard.round
            rw [if_neg (by rw [hne']; exact Bool.false_ne_true), hsbit]
            simp only [Bool.false_eq_true, if_false]
            rw [if_pos (Guard.content_of_not_empty hne')]
          rw [hrv1]; simp
        have hdig : sp.2.digits_ = 0 := by
          unfold Guard.empty Guard.unrecoverable at hemp; rw [Bool.and_eq_true] at hemp; exact beq_iff_eq.mp hemp.1
        have hxb : sp.2.xbit_ = false := by
          unfold Guard.empty Guard.unrecoverable at hemp; rw [Bool.and_eq_true, Bool.not_eq_true'] at hemp; exact hemp.2
        have hfrac0 : frac = 0 := represents_eq_zero_of_digits_zero_xbit_false hdig hxb hrep
        rw [hr, hval_frac, hfrac0]; simp

/-- **A fractional `ofNumber` (any mode) that lands on zero came from a source
below the smallest positive IOU value `10⁻⁸¹`.** The exponent-underflow flush to
zero happens in the `checked`/`iou`/`normalize` stage on the sub-`cMinOffset`
exponent, independent of the rounding mode: the 16-digit `normalizeToRange` output
sits below `cMinOffset`, so the 19-digit source exponent is `≤ -100` and its
mantissa keeps the value under `10¹⁹·10⁻¹⁰⁰ = 10⁻⁸¹`. Mode-generic companion of
`ofNumber_fractional_zero_below_min`; the deposit charge snaps upward, so it needs
the `.upward` instance. -/
lemma STAmount.ofNumber_iou_zero_below_min (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount) (hnt : nt.isIntegral = false)
    (hn : n.isNormalized) (hneg : n.negative_ = false) (hnz : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hz : result.mValue = 0) :
    n.toRat < (10 : ℚ) ^ (-81 : ℤ) := by
  have hnt_frac : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral mv mo ms msh => simp [NumericType.isIntegral] at hnt
  subst hnt_frac
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  have hwork : (if decide (n.signum < 0) then n.operator_neg else n) = n := by
    rw [hneg_dec]; simp
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true))] at hok
  rw [hwork] at hok
  rw [hneg_dec] at hok
  cases hnorm : n.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hexp_hi3 : n.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi n mode mant exp hr_lo hr_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts n mode mant exp hr_lo hr_hi (by omega) hexp_hi3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn hneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    have hexp_zero : exp < cMinOffset :=
      XRPL.Model.SingleAssetVault.STAmount.checked_iou_zero_exp mant.toUInt64 exp false mode
        hmtu_lo hmtu_hi (by omega) hexp_le result hok hz
    have hexp_n : n.exponent_ ≤ -100 := by unfold cMinOffset at hexp_zero; omega
    rw [Number.toRat_of_nonneg n hneg]
    have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hr_hi
    have hpe_pos : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
    have hstep : (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_
        < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ :=
      mul_lt_mul_of_pos_right hm hpe_pos
    have hle2 : (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ ≤ (10 : ℚ) ^ (-81 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 19, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    linarith [hstep, hle2]

/-- **An `.upward` integral `ofNumber` stores the ceiling** of a sign-cleared
normalized source: `n.toRat ≤ result.toRat`. Needs no nonzero hypothesis, so it also
rules out a positive source flushing to zero. -/
lemma STAmount.ofNumber_integral_upward_ge (nt : NumericType) (n : Number) (result : STAmount)
    (hint : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .upward = .ok result) :
    n.toRat ≤ result.toRat := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
  cases hr : n.to_rep .upward with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ :=
      XRPL.Model.SingleAssetVault.Number.to_rep_nonneg_range n .upward intValue hneg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    have hres_val : result.toRat = (intValue.toInt : ℚ) := by
      have hexact := STAmount.canonicalize_integral_toRat
        (STAmount.unchecked nt intValue.toUInt64 0 false) result .upward
        (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
        hval hok
      rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
      show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
      rw [toUInt64_toNat_of_nonneg intValue hnn]
    rw [hres_val]
    exact Number.to_rep_upward_ceil n intValue hn hneg hr

/-- **An `.upward` `ofNumber` never lowers a sign-cleared normalized source.** For an
integral type the stored value is the ceiling of `n` (`to_rep_upward_ceil`); for a
fractional type it is the 16-digit ceiling (`ofNumber_upward_floor_bounds`). Either
way `n.toRat ≤ result.toRat`, the lower `depositε` band's `Q ≤ charge` step. -/
lemma STAmount.ofNumber_upward_ge (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .upward = .ok result) (hres : result.mValue ≠ 0) :
    n.toRat ≤ result.toRat := by
  by_cases hint : nt.isIntegral = true
  · exact STAmount.ofNumber_integral_upward_ge nt n result hint hn hneg hok
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    have hn_ne : n.mantissa_ ≠ 0 :=
      STAmount.ofNumber_iou_mantissa_ne_zero nt n .upward result hnt_frac hok hres
    obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
      · exact hlo
    have hok' : STAmount.ofNumber .fractional n .upward = .ok result := by rw [← hnt_frac]; exact hok
    have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
      STAmount.ofNumber_iou_success_exp_range n .upward result hlo19 hhi19 hexp_lo hok' hres
    exact STAmount.ofNumber_upward_floor_bounds nt n result hnt_frac hneg hlo19 hhi19 hexp_lo
      hexp_hi hok hres

/-- **A 19-digit-normalized mantissa denoting a `≤16`-significant-digit value ends in
three zeros.** If `a·10^X = s·10^Y` with `10^18 ≤ a < 10^19` and `s < 10^16`, the exact
match forces `a = s·10^(Y-X)` with `Y-X ≥ 3`, so `1000 ∣ a`. -/
lemma sig16_normalized_mod1000 (a s : ℕ) (X Y : ℤ)
    (ha_lo : 10 ^ 18 ≤ a) (ha_hi : a < 10 ^ 19) (hs : s < 10 ^ 16)
    (heq : (a : ℚ) * (10 : ℚ) ^ X = (s : ℚ) * (10 : ℚ) ^ Y) :
    a % 1000 = 0 := by
  have h10ne : (10 : ℚ) ≠ 0 := by norm_num
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h; swap; · exact h
    exfalso
    have hz : (a : ℚ) * (10 : ℚ) ^ X = 0 := by rw [heq, h0]; simp
    have hne : (10 : ℚ) ^ X ≠ 0 := by positivity
    have haq : (a : ℚ) = 0 := (mul_eq_zero.mp hz).resolve_right hne
    have hapos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show 0 < a by omega)
    linarith
  have haeq : (s : ℚ) * (10 : ℚ) ^ (Y - X) = (a : ℚ) := by
    have key : (s : ℚ) * (10 : ℚ) ^ (Y - X) * (10 : ℚ) ^ X = (a : ℚ) * (10 : ℚ) ^ X := by
      rw [mul_assoc, ← zpow_add₀ h10ne, show (Y - X) + X = Y from by ring, ← heq]
    exact mul_right_cancel₀ (by positivity) key
  have h3 : (3 : ℤ) ≤ Y - X := by
    by_contra hlt
    push_neg at hlt
    have hle2 : Y - X ≤ 2 := by omega
    have hpow : (10 : ℚ) ^ (Y - X) ≤ (10 : ℚ) ^ (2 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) hle2
    have hp2 : (10 : ℚ) ^ (2 : ℤ) = 100 := by norm_num
    have hsq : (s : ℚ) < 10 ^ 16 := by exact_mod_cast hs
    have haq : (10 : ℚ) ^ 18 ≤ (a : ℚ) := by exact_mod_cast ha_lo
    have hsnn : (0 : ℚ) ≤ (s : ℚ) := by positivity
    have hub : (a : ℚ) ≤ (s : ℚ) * 100 := by rw [← haeq]; nlinarith [hpow, hp2, hsnn]
    nlinarith [hub, hsq, haq]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Y - X = (n : ℤ) := ⟨(Y - X).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hnge : 3 ≤ n := by omega
  have haeq2 : a = s * 10 ^ n := by
    have hcast : (a : ℚ) = ((s * 10 ^ n : ℕ) : ℚ) := by
      rw [← haeq, hn, zpow_natCast]; push_cast; ring
    exact_mod_cast hcast
  have hdvd : (1000 : ℕ) ∣ a := by
    rw [haeq2, show (1000 : ℕ) = 10 ^ 3 from by norm_num]
    exact Dvd.dvd.mul_left (pow_dvd_pow 10 hnge) s
  omega

/-- **`IOUAmount.normalize` is value-exact on a `≤16`-significant-digit mantissa.**
When `M = s·10^t` with `s < 10^16`, the 19-digit re-lift lands three-plus zeros below
the 16-digit window, so the re-round drops only trailing zeros. -/
lemma IOUAmount.normalize_sigdigits16 (M : UInt64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (s t : ℕ)
    (hMform : M.toNat = s * 10 ^ t) (hs : s < 10 ^ 16) (hMnz : M ≠ 0)
    (hfit : M.toNat < 2 ^ 63) (he_lo : -18 ≤ e) (he_hi : e ≤ 0)
    (hok : IOUAmount.normalize ⟨M.toInt64, e⟩ mode = .ok i) :
    i.toRat = (M.toNat : ℚ) * (10 : ℚ) ^ e := by
  have hmin : minExponent = -32768 := rfl
  have hmax : maxExponent = 32768 := rfl
  have hcmin : cMinOffset = -96 := rfl
  have hcmax : cMaxOffset = 80 := rfl
  have hMnz' : M.toNat ≠ 0 := fun h => hMnz (by rw [← UInt64.toNat_inj]; simpa using h)
  have hMtoInt : M.toInt64.toInt = (M.toNat : ℤ) := UInt64.toInt64_toInt_of_lt M hfit
  have hM19 : M.toNat < 10 ^ 19 := by omega
  have hne_min : M.toInt64 ≠ Int64.minValue := by
    intro h
    have h2 : M.toInt64.toInt = Int64.minValue.toInt := by rw [h]
    rw [hMtoInt, show Int64.minValue.toInt = (-9223372036854775808 : ℤ) from by decide] at h2
    omega
  obtain ⟨v, hfr, hvval, hvnorm⟩ := Number.from_rep_exact M.toInt64 e mode hne_min
    (by omega : minExponent + 18 ≤ e) (by omega : e ≤ maxExponent - 1)
  rw [hMtoInt] at hvval
  have hvpos : 0 < v.toRat := by rw [hvval]; positivity
  have hvm_ne : v.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero v h] at hvpos; exact lt_irrefl _ hvpos
  have hvneg : v.negative_ = false := by
    by_contra h
    rw [Bool.not_eq_false] at h
    linarith [Number.toRat_nonpos_of_negative v h, hvpos]
  obtain ⟨hvm_lo, hvm_hi⟩ := hvnorm.mantissaBounds_nat hvm_ne
  have hve_lo : minExponent ≤ v.exponent_ := by
    rcases hvnorm with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show v.mantissa_ = 0 by rw [h0]; rfl) hvm_ne
    · exact hlo
  have hve_hi : v.exponent_ ≤ maxExponent := by
    rcases hvnorm with h0 | ⟨_, _, _, _, hhi⟩
    · exact absurd (show v.mantissa_ = 0 by rw [h0]; rfl) hvm_ne
    · exact hhi
  have hvtoRat_form : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_
      = (s : ℚ) * (10 : ℚ) ^ ((t : ℤ) + e) := by
    have h1 : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ = v.toRat :=
      (Number.toRat_of_nonneg v hvneg).symm
    rw [h1, hvval, hMform]
    push_cast
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0), ← zpow_natCast (10:ℚ) t]
    ring
  have hmod : v.mantissa_.toNat % 1000 = 0 :=
    sig16_normalized_mod1000 v.mantissa_.toNat s v.exponent_ ((t : ℤ) + e)
      hvm_lo hvm_hi hs hvtoRat_form
  have hveq : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ = (M.toNat : ℚ) * (10:ℚ)^e := by
    rw [← Number.toRat_of_nonneg v hvneg]; exact hvval
  have hve_le0 : v.exponent_ ≤ 0 := by
    by_contra hgt
    push_neg at hgt
    have hge1 : (1 : ℤ) ≤ v.exponent_ := hgt
    have hlhs : (10 : ℚ) ^ 19 ≤ (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ := by
      have hm18 : (10 : ℚ) ^ 18 ≤ (v.mantissa_.toNat : ℚ) := by exact_mod_cast hvm_lo
      have hexp : (10 : ℚ) ^ (1 : ℤ) ≤ (10 : ℚ) ^ v.exponent_ :=
        zpow_le_zpow_right₀ (by norm_num) hge1
      have h181 : (10 : ℚ) ^ 19 = (10 : ℚ) ^ 18 * (10 : ℚ) ^ (1 : ℤ) := by norm_num
      have hmnn : (0:ℚ) ≤ (v.mantissa_.toNat : ℚ) := by positivity
      have hpnn : (0:ℚ) < (10:ℚ)^(1:ℤ) := by positivity
      calc (10:ℚ)^19 = (10:ℚ)^18 * (10:ℚ)^(1:ℤ) := h181
        _ ≤ (v.mantissa_.toNat : ℚ) * (10:ℚ)^(1:ℤ) := by nlinarith [hm18, hpnn]
        _ ≤ (v.mantissa_.toNat : ℚ) * (10:ℚ)^v.exponent_ := by nlinarith [hexp, hmnn]
    have hrhs : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ < (10 : ℚ) ^ 19 := by
      rw [hveq]
      have hMlt : (M.toNat : ℚ) < (10:ℚ)^19 := by exact_mod_cast hM19
      have hele : (10:ℚ)^e ≤ (10:ℚ)^(0:ℤ) := zpow_le_zpow_right₀ (by norm_num) he_hi
      have he0 : (10:ℚ)^(0:ℤ) = 1 := by norm_num
      have hMnn : (0:ℚ) ≤ (M.toNat : ℚ) := by positivity
      have hepos : (0:ℚ) < (10:ℚ)^e := by positivity
      nlinarith [hMlt, hele, he0, hMnn, hepos]
    linarith
  have hve_ge : (-99 : ℤ) ≤ v.exponent_ := by
    by_contra hlt
    push_neg at hlt
    have hle : v.exponent_ ≤ -100 := by omega
    have hlhs : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ < (10 : ℚ) ^ (-81 : ℤ) := by
      have hmlt : (v.mantissa_.toNat : ℚ) < (10 : ℚ) ^ 19 := by exact_mod_cast hvm_hi
      have hexp : (10 : ℚ) ^ v.exponent_ ≤ (10 : ℚ) ^ (-100 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hle
      have hsplit : (10:ℚ)^(19:ℕ) * (10:ℚ)^(-100:ℤ) = (10:ℚ)^(-81:ℤ) := by
        rw [show ((10:ℚ)^(19:ℕ)) = (10:ℚ)^(19:ℤ) by norm_num,
            ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
        norm_num
      have hmnn : (0:ℚ) ≤ (v.mantissa_.toNat : ℚ) := by positivity
      have hp100 : (0:ℚ) < (10:ℚ)^(-100:ℤ) := by positivity
      calc (v.mantissa_.toNat : ℚ) * (10:ℚ)^v.exponent_
          ≤ (v.mantissa_.toNat : ℚ) * (10:ℚ)^(-100:ℤ) := by nlinarith [hexp, hmnn]
        _ < (10:ℚ)^(19:ℕ) * (10:ℚ)^(-100:ℤ) := by nlinarith [hmlt, hp100]
        _ = (10:ℚ)^(-81:ℤ) := hsplit
    have hrhs : (10 : ℚ) ^ (-81 : ℤ) ≤ (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ := by
      rw [hveq]
      have hM1 : (1:ℚ) ≤ (M.toNat : ℚ) := by exact_mod_cast (show 1 ≤ M.toNat by omega)
      have hele : (10:ℚ)^(-18:ℤ) ≤ (10:ℚ)^e := zpow_le_zpow_right₀ (by norm_num) he_lo
      have hcmp : (10:ℚ)^(-81:ℤ) ≤ (10:ℚ)^(-18:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      have hepos : (0:ℚ) < (10:ℚ)^e := by positivity
      have hMnn : (0:ℚ) ≤ (M.toNat:ℚ) := by positivity
      nlinarith [hM1, hele, hcmp, hepos, hMnn]
    linarith
  have hntr := normalizeToRange_16_exact v mode hvm_lo hvm_hi hmod
    (by omega : minExponent ≤ v.exponent_ + 3) (by omega : v.exponent_ + 3 ≤ maxExponent)
  rw [hvneg] at hntr
  simp only [Bool.false_eq_true, if_false] at hntr
  have hfn : IOUAmount.fromNumber v mode
      = .ok ⟨(v.mantissa_ / 10 / 10 / 10).toInt64, v.exponent_ + 3⟩ := by
    unfold IOUAmount.fromNumber; rw [hntr]
  have hmant_ne : ¬ ((⟨M.toInt64, e⟩ : IOUAmount).mantissa_ == 0) = true := by
    show ¬ (M.toInt64 == 0) = true
    rw [beq_iff_eq]; intro h
    rw [h, show (0 : Int64).toInt = 0 from by decide] at hMtoInt
    omega
  unfold IOUAmount.normalize at hok
  rw [if_neg hmant_ne] at hok
  rw [show (⟨M.toInt64, e⟩ : IOUAmount).mantissa_ = M.toInt64 from rfl,
      show (⟨M.toInt64, e⟩ : IOUAmount).exponent_ = e from rfl, hfr] at hok
  simp only [] at hok
  rw [hfn] at hok
  simp only [] at hok
  rw [if_neg (by show ¬ (v.exponent_ + 3 > cMaxOffset); omega),
      if_neg (by show ¬ (v.exponent_ + 3 < cMinOffset); omega)] at hok
  have hieq : i = ⟨(v.mantissa_ / 10 / 10 / 10).toInt64, v.exponent_ + 3⟩ := (Except.ok.inj hok).symm
  rw [hieq, IOUAmount.toRat_eq]
  show ((v.mantissa_ / 10 / 10 / 10).toInt64.toInt : ℚ) * (10:ℚ)^(v.exponent_ + 3) = _
  have hdiv_lt : (v.mantissa_ / 10 / 10 / 10).toNat < 2 ^ 63 := by
    rw [m_div_thousand_toNat]; omega
  have hdiv_toInt : (v.mantissa_ / 10 / 10 / 10).toInt64.toInt
      = ((v.mantissa_.toNat / 1000 : ℕ) : ℤ) := by
    rw [UInt64.toInt64_toInt_of_lt _ hdiv_lt, m_div_thousand_toNat]
  rw [hdiv_toInt]
  have hdiv1000 : ((v.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000 = (v.mantissa_.toNat : ℚ) := by
    have hnat : v.mantissa_.toNat / 1000 * 1000 = v.mantissa_.toNat := Nat.div_mul_cancel (by omega)
    have := congrArg (Nat.cast (R := ℚ)) hnat
    push_cast at this ⊢; linarith
  have hexp3 : (10:ℚ)^(v.exponent_ + 3) = (10:ℚ)^v.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
  rw [hexp3]
  calc ((v.mantissa_.toNat / 1000 : ℕ) : ℚ) * ((10:ℚ)^v.exponent_ * 1000)
      = (((v.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000) * (10:ℚ)^v.exponent_ := by ring
    _ = (v.mantissa_.toNat : ℚ) * (10:ℚ)^v.exponent_ := by rw [hdiv1000]
    _ = (M.toNat : ℚ) * (10:ℚ)^e := hveq

/-- **`STAmount.checked` on a `.fractional` type is value-exact on a `≤16`-significant-digit
mantissa.** Routes the canonicalize IOU pack through `normalize_sigdigits16`. -/
lemma STAmount.checked_frac_sigdigits_exact (M : UInt64) (e : Int) (mode : rounding_mode)
    (c : STAmount) (s t : ℕ)
    (hMform : M.toNat = s * 10 ^ t) (hs : s < 10 ^ 16) (hMnz : M ≠ 0)
    (hfit : M.toNat < 2 ^ 63) (he_lo : -18 ≤ e) (he_hi : e ≤ 0)
    (hok : STAmount.checked .fractional M e false mode = .ok c) :
    c.toRat = (M.toNat : ℚ) * (10 : ℚ) ^ e := by
  have hMnz' : M.toNat ≠ 0 := fun h => hMnz (by rw [← UInt64.toNat_inj]; simpa using h)
  set s0 : STAmount := STAmount.unchecked .fractional M e false with hs0
  have h_int : ¬ s0.integral = true := by
    rw [hs0]; simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have hsd_eq : s0.signedDrops.toInt64 = M.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt_of_lt s0 (show s0.mValue.toNat < 2 ^ 63 from hfit),
        UInt64.toInt64_toInt_of_lt M hfit]
    show s0.signedDrops = (M.toNat : ℤ)
    simp [hs0, STAmount.signedDrops, STAmount.unchecked]
  have hiou : s0.iou mode = IOUAmount.normalize ⟨M.toInt64, e⟩ mode := by
    unfold STAmount.iou; rw [if_neg h_int]
    show IOUAmount.ofMantissaExp s0.signedDrops.toInt64 s0.mOffset mode
      = IOUAmount.normalize ⟨M.toInt64, e⟩ mode
    rw [hsd_eq]; rfl
  rw [STAmount.checked] at hok
  unfold STAmount.canonicalize at hok
  rw [if_neg h_int, hiou] at hok
  cases h_norm : IOUAmount.normalize ⟨M.toInt64, e⟩ mode with
  | error err => rw [h_norm] at hok; simp at hok
  | ok i =>
    rw [h_norm] at hok; simp only [] at hok
    have hres_eq : c = ⟨.fractional,
        (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64,
        i.exponent_, decide (i.signum < 0)⟩ := (Except.ok.inj hok).symm
    have hival : i.toRat = (M.toNat : ℚ) * (10 : ℚ) ^ e :=
      IOUAmount.normalize_sigdigits16 M e mode i s t hMform hs hMnz hfit he_lo he_hi h_norm
    have himne : i.mantissa_ ≠ 0 := by
      intro h0
      have h0r : i.toRat = 0 := by rw [IOUAmount.toRat_eq, h0]; simp
      rw [hival] at h0r
      have hpos : (0 : ℚ) < (M.toNat : ℚ) * (10 : ℚ) ^ e :=
        mul_pos (by exact_mod_cast (show 0 < M.toNat by omega)) (by positivity)
      linarith
    have hr16 : i.InRange16 :=
      (IOUAmount.normalize_InRange16_or_zero ⟨M.toInt64, e⟩ mode i h_norm).resolve_right himne
    rw [hres_eq, STAmount.iou_pack_toRat i hr16, hival]

/-- **The floor of `A·10^P` has at most `16` significant digits** when `A < 10^16`. For
`P ≥ 0` it is `A·10^P` (trailing zeros); for `P < 0` it is below `A`. -/
lemma floor_nat_mul_zpow_sigform (A : ℕ) (P : ℤ) (hA : A < 10 ^ 16) :
    ∃ s t : ℕ, (⌊(A : ℚ) * (10 : ℚ) ^ P⌋).toNat = s * 10 ^ t ∧ s < 10 ^ 16 := by
  by_cases hP : 0 ≤ P
  · refine ⟨A, P.toNat, ?_, hA⟩
    have hPeq : (10 : ℚ) ^ P = (10 : ℚ) ^ P.toNat := by
      rw [← zpow_natCast (10 : ℚ) P.toNat, Int.toNat_of_nonneg hP]
    have hcast : (A : ℚ) * (10 : ℚ) ^ P = ((A * 10 ^ P.toNat : ℕ) : ℚ) := by
      rw [hPeq]; push_cast; ring
    rw [hcast, Int.floor_natCast, Int.toNat_natCast]
  · refine ⟨(⌊(A : ℚ) * (10 : ℚ) ^ P⌋).toNat, 0, by rw [pow_zero, mul_one], ?_⟩
    have hPlt : P ≤ 0 := le_of_lt (not_le.mp hP)
    have h10 : (10 : ℚ) ^ P ≤ 1 := by
      calc (10 : ℚ) ^ P ≤ (10 : ℚ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hPlt
        _ = 1 := by norm_num
    have hle : (A : ℚ) * (10 : ℚ) ^ P ≤ (A : ℚ) := by
      nlinarith [h10, (show (0 : ℚ) ≤ (A : ℚ) from by positivity)]
    have hfl : ⌊(A : ℚ) * (10 : ℚ) ^ P⌋ ≤ (A : ℤ) := by
      calc ⌊(A : ℚ) * (10 : ℚ) ^ P⌋ ≤ ⌊(A : ℚ)⌋ := Int.floor_le_floor hle
        _ = (A : ℤ) := Int.floor_natCast A
    omega

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Abstract-real arithmetic for the multiplication-underflow charge bound: when the
product `navN·s` is below `t`, the ideal `nav·s/ST` (with `nav ≤ 2·navN`, `ST ≥ 1`)
stays below `8·t`. Kept over plain reals so the solver never touches the vault. -/
private lemma charge_underflow_mul (nav s ST navN t : ℚ)
    (hs : 0 < s) (hnav : 0 < nav) (hST : 1 ≤ ST) (ht : 0 < t)
    (hnav_le : nav ≤ navN * 2) (hmul : navN * s < t) :
    nav * s / ST < 8 * t := by
  have hSTpos : 0 < ST := by linarith
  have h1 : nav * s / ST ≤ nav * s := by
    rw [div_le_iff₀ hSTpos]; nlinarith [mul_pos hnav hs]
  nlinarith [h1, hnav_le, hs, hmul, ht]

/-- Abstract-real arithmetic for the division-underflow charge bound: when `P/ST` is
below `t`, the ideal `nav·s/ST` (with `nav ≤ 2·navN`, `navN·s` within the mul error of
`P`) stays below `8·t`. -/
private lemma charge_underflow_div (nav s ST navN P t : ℚ)
    (hs : 0 < s) (hnavN : 0 < navN) (_hnav : 0 < nav) (hSTpos : 0 < ST) (ht : 0 < t)
    (hnav_le : nav ≤ navN * 2)
    (hmul : |P - navN * s| ≤ |navN * s| * (5 / (2 ^ 63 + 7)))
    (hdiv : |P / ST| < t) :
    nav * s / ST < 8 * t := by
  have hnavN_s_pos : 0 < navN * s := mul_pos hnavN hs
  rw [abs_of_pos hnavN_s_pos] at hmul
  have hmb := abs_le.mp hmul
  have hPpos : 0 < P := by nlinarith [hmb.1, hnavN_s_pos]
  have hPST : P / ST < t := by rw [abs_of_pos (div_pos hPpos hSTpos)] at hdiv; exact hdiv
  have hNAV : navN * s ≤ P * 2 := by nlinarith [hmb.2, hnavN_s_pos]
  have hnavs : nav * s ≤ 4 * P := by nlinarith [hnav_le, hs, hNAV]
  have hle4 : nav * s / ST ≤ 4 * (P / ST) := by
    rw [div_le_iff₀ hSTpos, show 4 * (P / ST) * ST = 4 * P from by
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hSTpos)]]
    exact hnavs
  linarith [hle4, hPST]

/-- **The charge's pre-round `Number` `Q` and its two-sided pipeline bound**, on a
nonempty vault. The charge `c = ofNumber v.numericType Q .upward` prices the shares
through `sub`/`mul`/`div`; `Q` sits within `depositε` of the exact ideal charge when
`Q` is nonzero, and is `Number`-underflow tiny when `Q` is zero. `hnavm_sub` records
that the net asset value did not underflow to zero (in a real deposit the shares
side divides by it, so a `.ok` run forces it nonzero). Deposit-charge analog of
`recovery_pipeline_bound`. -/
lemma sharesToAssetsDeposit_charge_nonempty (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    ∃ Q : Number,
      STAmount.ofNumber v.numericType Q .upward = .ok c ∧
      0 < v.idealChargeDeposit shares.toRat ∧
      (Q.mantissa_ ≠ 0 → Q.isNormalized ∧ Q.negative_ = false ∧
        |Q.toRat - v.idealChargeDeposit shares.toRat|
          ≤ v.idealChargeDeposit shares.toRat * depositε) ∧
      (Q.mantissa_ = 0 →
        v.idealChargeDeposit shares.toRat ≤ (10 : ℚ) ^ (-32700 : ℤ)) := by
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
    have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
      absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
    have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have : (0 : ℚ) < (v.toExact.sharesTotal : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hne
    rw [hST_def, ← hcast]; exact this
  have hST_one : 1 ≤ ST := by
    have hnum_pos : 0 < ST.num := Rat.num_pos.mpr hST_pos
    have hcast : ST = (ST.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den ST]
      rw [hST_def, v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [← hST_def]; exact ne_of_gt hST_pos)
  have hideal : v.idealChargeDeposit s = nav * s / ST := by
    unfold RawVault.idealChargeDeposit
    rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hidpos : 0 < nav * s / ST := div_pos (mul_pos hnav_pos hshpos) hST_pos
  -- reduce the charge pipeline
  unfold sharesToAssetsDeposit at hsad
  rw [if_neg hmz] at hsad
  obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
  set navN := v.assetsTotal with hnavN_eq
  obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  have hnavm : navN.mantissa_ ≠ 0 := hmz
  have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
  obtain ⟨_, hnavbound, _, hnavN_pos⟩ := Vault.depositNav_facts v navN hmz hnavm hnavN_eq
  obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
    STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
  have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
  rw [hshNeq] at hsnval hsnnorm
  have hshN_val : shN.toRat = s := by rw [hsnval]
  have hshN_pos : 0 < shN.toRat := by rw [hshN_val]; exact hshpos
  have hshNm : shN.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hshN_val]; exact ne_of_gt hshpos)
  have hnN_le : navN.toRat ≤ nav * (1 + 6 / (2 ^ 63 - 3)) := by
    have := abs_le.mp hnavbound; nlinarith
  have hnav_le_nN : nav ≤ navN.toRat * 2 := by
    have := abs_le.mp hnavbound; nlinarith [hnavN_pos]
  refine ⟨Q, hc, by rw [hideal]; exact hidpos, ?_, ?_⟩
  · -- nonzero `Q`: run the relative composition
    intro hQm
    have hPm : P.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
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
    have hsubb : |navN.toRat - nav| ≤ nav * (6 / (2 ^ 63 - 3)) := hnavbound
    have hPpos : 0 < P.toRat := by
      have := abs_le.mp hmulb
      have hε : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      nlinarith [mul_pos hnavN_pos hshN_pos]
    have hPN_pos : 0 < P.toRat / ST := div_pos hPpos hST_pos
    have hdivb : |Q.toRat - P.toRat / ST| ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) := by
      have h : |Q.toRat - P.toRat / ST| ≤ |P.toRat / ST| * (6 / (2 ^ 63 - 3)) :=
        operator_div_rounds_to_nearest P v.sharesTotal Q hPnorm v.wf.sharesTotal_norm hQ hQm
      rwa [abs_of_pos hPN_pos] at h
    have hQpos : 0 < Q.toRat := by
      have := abs_le.mp hdivb; nlinarith
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
    have h3 : |Q.toRat * ST - P.toRat| ≤ P.toRat * (6 / (2 ^ 63 - 3)) := by
      have hrw : Q.toRat * ST - P.toRat = (Q.toRat - P.toRat / ST) * ST := by field_simp
      calc |Q.toRat * ST - P.toRat|
          = |Q.toRat - P.toRat / ST| * ST := by rw [hrw, abs_mul, abs_of_pos hST_pos]
        _ ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) * ST := by
              nlinarith [hST_pos, abs_nonneg (Q.toRat - P.toRat / ST), hdivb]
        _ = P.toRat * (6 / (2 ^ 63 - 3)) := by
              rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hST_pos)]
    have hcomp := div_pipeline_rel_bound ST ST (nav * s) P.toRat Q.toRat 0
      (12 / (2 ^ 63 - 3)) (6 / (2 ^ 63 - 3)) depositε
      (mul_pos hnav_pos hshpos) (le_of_lt hQpos)
      (by rw [sub_self, abs_zero, mul_zero])
      h2 h3 (le_refl 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      charge_pipeline_up charge_pipeline_lo
    have hQneg : Q.negative_ = false := Number.negative_false_of_pos Q hQpos
    refine ⟨hQnorm, hQneg, ?_⟩
    -- convert `|Q·ST - nav·s| ≤ nav·s·ε` to `|Q - ideal| ≤ ideal·ε`
    rw [hideal]
    have heq : Q.toRat - nav * s / ST = (Q.toRat * ST - nav * s) / ST := by field_simp
    rw [heq, abs_div, abs_of_pos hST_pos, div_le_iff₀ hST_pos]
    calc |Q.toRat * ST - nav * s| ≤ nav * s * depositε := hcomp
      _ = nav * s / ST * depositε * ST := by field_simp
  · -- zero `Q`: the pipeline underflowed, so the ideal is `Number`-tiny
    intro hQm0
    rw [hideal]
    have hsmallmul : P.mantissa_ = 0 →
        |navN.toRat * shN.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) :=
      fun hP0 => operator_mul_underflow_truth_small navN shN P .to_nearest
        hnavnorm hsnnorm hnavm hshNm hP hP0
    have hmulbnd : P.mantissa_ ≠ 0 →
        |P.toRat - navN.toRat * shN.toRat| ≤ |navN.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
      fun hPnm => operator_mul_rounds_to_nearest navN shN P hnavnorm hsnnorm hP hPnm
    have hdivund : P.mantissa_ ≠ 0 →
        |P.toRat / ST| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) :=
      fun hPnm => operator_div_underflow_truth_small P v.sharesTotal Q .to_nearest
        (operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPnm)
        v.wf.sharesTotal_norm hPnm hSTm hQ hQm0
    have hunit : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) = (10 : ℚ) ^ (-32750 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num [minExponent]
    have hu_pos : (0 : ℚ) < (10 : ℚ) ^ (-32750 : ℤ) := zpow_pos (by norm_num) _
    have h_le : 8 * (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-32700 : ℤ) := by
      rw [show (10 : ℚ) ^ (-32700 : ℤ) = (10 : ℚ) ^ (50 : ℤ) * (10 : ℚ) ^ (-32750 : ℤ) from by
        rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num]
      nlinarith [hu_pos, show (8 : ℚ) ≤ (10 : ℚ) ^ (50 : ℤ) from by norm_num]
    have hbound : nav * s / ST < 8 * (10 : ℚ) ^ (-32750 : ℤ) := by
      by_cases hPm0 : P.mantissa_ = 0
      · -- multiplication underflowed: `navN·s` is tiny
        have hsmall := hsmallmul hPm0
        rw [abs_of_pos (mul_pos hnavN_pos hshN_pos), hunit, hshN_val] at hsmall
        exact charge_underflow_mul nav s ST navN.toRat _ hshpos hnav_pos hST_one hu_pos
          hnav_le_nN hsmall
      · -- division underflowed: `P/ST` is tiny, and `nav·s/ST ≤ 4·(P/ST)`
        have hsmall := hdivund hPm0
        rw [hunit] at hsmall
        have hmulbound := hmulbnd hPm0
        rw [hshN_val] at hmulbound
        exact charge_underflow_div nav s ST navN.toRat P.toRat _ hshpos hnavN_pos hnav_pos
          hST_pos hu_pos hnav_le_nN hmulbound hsmall
    linarith [hbound, h_le]

/-- Closure of the charge `sub`/`mul`/`div` pipeline within the raw
`19/(2^63-3)` (upper side). -/
lemma charge_pipeline_up19 :
    ((1 : ℚ) + 12 / (2 ^ 63 - 3)) * (1 + 6 / (2 ^ 63 - 3))
      ≤ (1 + 19 / (2 ^ 63 - 3)) * (1 - 0) := by norm_num

/-- Closure of the charge `sub`/`mul`/`div` pipeline within the raw
`19/(2^63-3)` (lower side). -/
lemma charge_pipeline_lo19 :
    ((1 : ℚ) - 19 / (2 ^ 63 - 3)) * (1 + 0)
      ≤ (1 - 12 / (2 ^ 63 - 3)) * (1 - 6 / (2 ^ 63 - 3)) := by norm_num

/-- Composition-grade sibling of `sharesToAssetsDeposit_charge_nonempty`: the charge
`Q` band at the raw pipeline constant `19/(2^63-3)` (rather than the widened
`depositε`), and the underflow ideal at the tight `8·10^(-32750)`. The dilution
composition needs this tighter granularity; the `depositε`-level lemma stays as the
headline-grade statement. -/
lemma sharesToAssetsDeposit_charge_nonempty_raw (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    ∃ Q : Number,
      STAmount.ofNumber v.numericType Q .upward = .ok c ∧
      0 < v.idealChargeDeposit shares.toRat ∧
      (Q.mantissa_ ≠ 0 → Q.isNormalized ∧ Q.negative_ = false ∧
        |Q.toRat - v.idealChargeDeposit shares.toRat|
          ≤ v.idealChargeDeposit shares.toRat * (19 / (2 ^ 63 - 3))) ∧
      (Q.mantissa_ = 0 →
        v.idealChargeDeposit shares.toRat < 8 * (10 : ℚ) ^ (-32750 : ℤ)) := by
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
    have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
      absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
    have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have : (0 : ℚ) < (v.toExact.sharesTotal : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hne
    rw [hST_def, ← hcast]; exact this
  have hST_one : 1 ≤ ST := by
    have hnum_pos : 0 < ST.num := Rat.num_pos.mpr hST_pos
    have hcast : ST = (ST.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den ST]
      rw [hST_def, v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [← hST_def]; exact ne_of_gt hST_pos)
  have hideal : v.idealChargeDeposit s = nav * s / ST := by
    unfold RawVault.idealChargeDeposit
    rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hidpos : 0 < nav * s / ST := div_pos (mul_pos hnav_pos hshpos) hST_pos
  unfold sharesToAssetsDeposit at hsad
  rw [if_neg hmz] at hsad
  obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
  set navN := v.assetsTotal with hnavN_eq
  obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  have hnavm : navN.mantissa_ ≠ 0 := hmz
  have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
  obtain ⟨_, hnavbound, _, hnavN_pos⟩ := Vault.depositNav_facts v navN hmz hnavm hnavN_eq
  obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
    STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
  have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
  rw [hshNeq] at hsnval hsnnorm
  have hshN_val : shN.toRat = s := by rw [hsnval]
  have hshN_pos : 0 < shN.toRat := by rw [hshN_val]; exact hshpos
  have hshNm : shN.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hshN_val]; exact ne_of_gt hshpos)
  have hnN_le : navN.toRat ≤ nav * (1 + 6 / (2 ^ 63 - 3)) := by
    have := abs_le.mp hnavbound; nlinarith
  have hnav_le_nN : nav ≤ navN.toRat * 2 := by
    have := abs_le.mp hnavbound; nlinarith [hnavN_pos]
  refine ⟨Q, hc, by rw [hideal]; exact hidpos, ?_, ?_⟩
  · intro hQm
    have hPm : P.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
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
    have hsubb : |navN.toRat - nav| ≤ nav * (6 / (2 ^ 63 - 3)) := hnavbound
    have hPpos : 0 < P.toRat := by
      have := abs_le.mp hmulb
      have hε : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      nlinarith [mul_pos hnavN_pos hshN_pos]
    have hPN_pos : 0 < P.toRat / ST := div_pos hPpos hST_pos
    have hdivb : |Q.toRat - P.toRat / ST| ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) := by
      have h : |Q.toRat - P.toRat / ST| ≤ |P.toRat / ST| * (6 / (2 ^ 63 - 3)) :=
        operator_div_rounds_to_nearest P v.sharesTotal Q hPnorm v.wf.sharesTotal_norm hQ hQm
      rwa [abs_of_pos hPN_pos] at h
    have hQpos : 0 < Q.toRat := by
      have := abs_le.mp hdivb; nlinarith
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
    have h3 : |Q.toRat * ST - P.toRat| ≤ P.toRat * (6 / (2 ^ 63 - 3)) := by
      have hrw : Q.toRat * ST - P.toRat = (Q.toRat - P.toRat / ST) * ST := by field_simp
      calc |Q.toRat * ST - P.toRat|
          = |Q.toRat - P.toRat / ST| * ST := by rw [hrw, abs_mul, abs_of_pos hST_pos]
        _ ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) * ST := by
              nlinarith [hST_pos, abs_nonneg (Q.toRat - P.toRat / ST), hdivb]
        _ = P.toRat * (6 / (2 ^ 63 - 3)) := by
              rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hST_pos)]
    have hcomp := div_pipeline_rel_bound ST ST (nav * s) P.toRat Q.toRat 0
      (12 / (2 ^ 63 - 3)) (6 / (2 ^ 63 - 3)) (19 / (2 ^ 63 - 3))
      (mul_pos hnav_pos hshpos) (le_of_lt hQpos)
      (by rw [sub_self, abs_zero, mul_zero])
      h2 h3 (le_refl 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      charge_pipeline_up19 charge_pipeline_lo19
    have hQneg : Q.negative_ = false := Number.negative_false_of_pos Q hQpos
    refine ⟨hQnorm, hQneg, ?_⟩
    rw [hideal]
    have heq : Q.toRat - nav * s / ST = (Q.toRat * ST - nav * s) / ST := by field_simp
    rw [heq, abs_div, abs_of_pos hST_pos, div_le_iff₀ hST_pos]
    calc |Q.toRat * ST - nav * s| ≤ nav * s * (19 / (2 ^ 63 - 3)) := hcomp
      _ = nav * s / ST * (19 / (2 ^ 63 - 3)) * ST := by field_simp
  · intro hQm0
    rw [hideal]
    have hsmallmul : P.mantissa_ = 0 →
        |navN.toRat * shN.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) :=
      fun hP0 => operator_mul_underflow_truth_small navN shN P .to_nearest
        hnavnorm hsnnorm hnavm hshNm hP hP0
    have hmulbnd : P.mantissa_ ≠ 0 →
        |P.toRat - navN.toRat * shN.toRat| ≤ |navN.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
      fun hPnm => operator_mul_rounds_to_nearest navN shN P hnavnorm hsnnorm hP hPnm
    have hdivund : P.mantissa_ ≠ 0 →
        |P.toRat / ST| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) :=
      fun hPnm => operator_div_underflow_truth_small P v.sharesTotal Q .to_nearest
        (operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPnm)
        v.wf.sharesTotal_norm hPnm hSTm hQ hQm0
    have hunit : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) = (10 : ℚ) ^ (-32750 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num [minExponent]
    have hu_pos : (0 : ℚ) < (10 : ℚ) ^ (-32750 : ℤ) := zpow_pos (by norm_num) _
    have hbound : nav * s / ST < 8 * (10 : ℚ) ^ (-32750 : ℤ) := by
      by_cases hPm0 : P.mantissa_ = 0
      · have hsmall := hsmallmul hPm0
        rw [abs_of_pos (mul_pos hnavN_pos hshN_pos), hunit, hshN_val] at hsmall
        exact charge_underflow_mul nav s ST navN.toRat _ hshpos hnav_pos hST_one hu_pos
          hnav_le_nN hsmall
      · have hsmall := hdivund hPm0
        rw [hunit] at hsmall
        have hmulbound := hmulbnd hPm0
        rw [hshN_val] at hmulbound
        exact charge_underflow_div nav s ST navN.toRat P.toRat _ hshpos hnavN_pos hnav_pos
          hST_pos hu_pos hnav_le_nN hmulbound hsmall
    exact hbound

/-- **The full charge accuracy bound**, both numeric kinds and both vault regimes.
On an empty vault the charge equals the ideal exactly (`checked`-exact: integral
inline, fractional via `hfrac_exact`); on a nonempty vault the upward snap of the
pipeline `Q` gives the lower `depositε` band and the `2·10^exponent` overcharge for a
nonzero charge, and forces the ideal below the type's grid minimum when it flushes to
zero. `hnavm_sub` (net asset value nonzero, from the shares-side division) is threaded
from the caller. -/
lemma sharesToAssetsDeposit_charge_bound (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hfrac_exact : v.assetsTotal.mantissa_ = 0 → v.numericType.isIntegral = false →
      c.toRat = v.idealChargeDeposit shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    0 ≤ v.idealChargeDeposit shares.toRat ∧
    (c.isZero = false →
      v.idealChargeDeposit shares.toRat * (1 - depositε) ≤ c.toRat) ∧
    (c.isZero = true →
      v.idealChargeDeposit shares.toRat * (1 - depositε) <
        if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) ∧
    (c.isZero = false →
      c.toRat - v.idealChargeDeposit shares.toRat ≤
        v.idealChargeDeposit shares.toRat * depositε + 2 * (10 : ℚ) ^ c.exponent) := by
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  set I : ℚ := v.idealChargeDeposit shares.toRat with hI_def
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: the charge equals the ideal exactly
    have hA0 : v.toExact.assetsTotal = 0 := Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal hmz
    have hI_eq : I = shares.toRat / (10 : ℚ) ^ v.scale.toNat := by
      rw [hI_def]; unfold RawVault.idealChargeDeposit; rw [if_pos hA0]
    have hI_pos : 0 < I := by rw [hI_eq]; exact div_pos hshpos (by positivity)
    have hcval : c.toRat = I := by
      by_cases hint : v.numericType.isIntegral = true
      · -- empty integral: `checked` reproduces the integer `shares`
        have hshmax : shares.mValue.toNat ≤ maxRep.toNat := by
          have hr := hshc.in_range; rw [hshnt] at hr
          calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
            _ = maxRep.toNat := by decide
        have hscale : v.scale = 0 := v.wf.scale_integral hint
        have hshexp : shares.exponent = 0 := hshc.offset_zero
        have hideal_sh : I = shares.toRat := by
          rw [hI_eq, hscale]; show shares.toRat / (10 : ℚ) ^ (0 : UInt8).toNat = shares.toRat
          norm_num
        unfold sharesToAssetsDeposit at hsad
        rw [if_pos hmz] at hsad
        obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
        have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
        rw [hceq, STAmount.checked] at hc
        have hoff0 : (STAmount.unchecked v.numericType shares.mantissa
            (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
          show shares.exponent - (v.scale.toNat : ℤ) = 0
          rw [hshexp, hscale]; rfl
        have hval0 : (STAmount.unchecked v.numericType shares.mantissa
            (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := hshmax
        have hcval2 := STAmount.canonicalize_integral_toRat _ c .to_nearest
          (show (STAmount.unchecked v.numericType shares.mantissa
            (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff0 hval0 hc
        have hun : (STAmount.unchecked v.numericType shares.mantissa
            (shares.exponent - (v.scale.toNat : ℤ)) false).toRat = (shares.mValue.toNat : ℚ) := by
          rw [STAmount.toRat_of_offset_zero _ hoff0]
          unfold STAmount.signedDrops STAmount.unchecked STAmount.mantissa; simp
        have hsh : shares.toRat = (shares.mValue.toNat : ℚ) := by
          rw [STAmount.toRat_of_offset_zero shares hshexp]
          unfold STAmount.signedDrops
          rw [STAmount.mIsNegative_false_of_pos shares hshpos]; simp
        rw [hcval2, hun, ← hsh, hideal_sh]
      · -- empty fractional: exactness supplied by the caller
        have hintf : v.numericType.isIntegral = false := by
          cases h : v.numericType.isIntegral with
          | true => exact absurd h hint
          | false => rfl
        rw [hI_def]; exact hfrac_exact hmz hintf
    have hc0 : c.mValue ≠ 0 := fun h => by
      have := (STAmount.toRat_eq_zero_iff c).mpr h; rw [hcval] at this; linarith [hI_pos]
    have hcnz : c.isZero = false := by
      rw [STAmount.isZero]; exact beq_eq_false_iff_ne.mpr hc0
    refine ⟨le_of_lt hI_pos, ?_, ?_, ?_⟩
    · intro _; rw [hcval]; nlinarith [hI_pos, hεnn]
    · intro hz; rw [hcnz] at hz; exact absurd hz (by decide)
    · intro _; rw [hcval, sub_self]
      have h1 : (0 : ℚ) ≤ I * depositε := mul_nonneg (le_of_lt hI_pos) hεnn
      have h2 : (0 : ℚ) ≤ 2 * (10 : ℚ) ^ c.exponent := by positivity
      linarith
  · -- nonempty vault: the pipeline `Q` and its snap
    obtain ⟨Q, hc, hidpos, hQnz, hQz⟩ :=
      sharesToAssetsDeposit_charge_nonempty v shares c hshc hshnt hshpos hmz hsad
    rw [← hI_def] at hidpos hQnz hQz
    have hfrac_of : v.numericType.isIntegral = false → v.numericType = .fractional := by
      intro hf; cases hnt : v.numericType with
      | fractional => rfl
      | integral mv mo ms msh => rw [hnt] at hf; simp [NumericType.isIntegral] at hf
    have hQpos_of : Q.mantissa_ ≠ 0 → Q.negative_ = false → 0 < Q.toRat := by
      intro hQm hQneg
      have hnn : 0 ≤ Q.toRat := by rw [Number.toRat_of_nonneg Q hQneg]; positivity
      exact lt_of_le_of_ne hnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero Q hQm))
    have hQm_of : c.mValue ≠ 0 → Q.mantissa_ ≠ 0 := by
      intro hc0
      by_cases hint : v.numericType.isIntegral = true
      · exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .upward c hint hc hc0
      · exact STAmount.ofNumber_iou_mantissa_ne_zero v.numericType Q .upward c
          (hfrac_of (by cases h : v.numericType.isIntegral with
            | true => exact absurd h hint | false => rfl)) hc hc0
    refine ⟨le_of_lt hidpos, ?_, ?_, ?_⟩
    · -- lower band `I·(1-ε) ≤ c`
      intro hcnz
      have hc0 : c.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hcnz; exact hcnz)
      obtain ⟨hQnorm, hQneg, hQbound⟩ := hQnz (hQm_of hc0)
      have hQlo : I * (1 - depositε) ≤ Q.toRat := by
        have := abs_le.mp hQbound; nlinarith [this.1]
      have hQlec : Q.toRat ≤ c.toRat :=
        STAmount.ofNumber_upward_ge v.numericType Q c hQnorm hQneg hc hc0
      linarith
    · -- zero charge: the ideal is below the grid minimum
      intro hcz
      have hc0 : c.mValue = 0 := by
        have := hcz; rw [STAmount.isZero] at this; exact beq_iff_eq.mp this
      by_cases hQm : Q.mantissa_ = 0
      · -- pipeline underflowed: the ideal is `Number`-tiny, below either grid step
        have hid_small := hQz hQm
        have hbig : (10 : ℚ) ^ (-32700 : ℤ) <
            if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ) := by
          split
          · calc (10 : ℚ) ^ (-32700 : ℤ) < (10 : ℚ) ^ (0 : ℤ) :=
                  zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
              _ = 1 := by norm_num
          · exact zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
        nlinarith [hid_small, hbig, mul_nonneg (le_of_lt hidpos) hεnn]
      · -- the snap floored a nonzero `Q` to zero
        obtain ⟨hQnorm, hQneg, hQbound⟩ := hQnz hQm
        have hQlo : I * (1 - depositε) ≤ Q.toRat := by
          have := abs_le.mp hQbound; nlinarith [this.1]
        by_cases hint : v.numericType.isIntegral = true
        · -- integral: a positive `Q` can never ceil to zero, so this case is vacuous
          exfalso
          have hQpos := hQpos_of hQm hQneg
          have hge := STAmount.ofNumber_integral_upward_ge v.numericType Q c hint hQnorm hQneg hc
          have hc_zero : c.toRat = 0 := (STAmount.toRat_eq_zero_iff c).mpr hc0
          linarith
        · rw [if_neg hint]
          have hintf : v.numericType.isIntegral = false := by
            cases h : v.numericType.isIntegral with
            | true => exact absurd h hint | false => rfl
          have hbelow : Q.toRat < (10 : ℚ) ^ (-81 : ℤ) :=
            STAmount.ofNumber_iou_zero_below_min v.numericType Q .upward c hintf hQnorm hQneg hQm hc hc0
          linarith
    · -- overcharge `c - I ≤ I·ε + 2·10^exponent`
      intro hcnz
      have hc0 : c.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hcnz; exact hcnz)
      obtain ⟨hQnorm, hQneg, hQbound⟩ := hQnz (hQm_of hc0)
      have hQup : Q.toRat ≤ I * (1 + depositε) := by
        have := abs_le.mp hQbound; nlinarith [this.2]
      have hc_le : c.toRat ≤ Q.toRat + 2 * (10 : ℚ) ^ c.exponent := by
        by_cases hint : v.numericType.isIntegral = true
        · have hwithin := STAmount.ofNumber_integral_within_one v.numericType Q .upward c
            hint hQnorm hQneg hc
          have hcexp : c.exponent = 0 :=
            (sharesToAssetsDeposit_integral_canonical v shares c hint hsad).1.offset_zero
          rw [hcexp]
          have := (abs_lt.mp hwithin).2; simp only [zpow_zero]; linarith
        · have hQm := hQm_of hc0
          obtain ⟨hr_lo, hr_hi⟩ := hQnorm.mantissaBounds_nat hQm
          have hre_lo : minExponent ≤ Q.exponent_ := by
            rcases hQnorm with h0 | ⟨_, _, _, hlo, _⟩
            · exact absurd (show Q.mantissa_ = 0 by rw [h0]; rfl) hQm
            · exact hlo
          have hintf : v.numericType.isIntegral = false := by
            cases h : v.numericType.isIntegral with
            | true => exact absurd h hint | false => rfl
          have hfrac : v.numericType = .fractional := hfrac_of hintf
          have hok' : STAmount.ofNumber .fractional Q .upward = .ok c := by rw [← hfrac]; exact hc
          have hre_hi : Q.exponent_ + 4 ≤ maxExponent :=
            STAmount.ofNumber_iou_success_exp_range Q .upward c hr_lo hr_hi hre_lo hok' hc0
          have hceil := STAmount.ofNumber_upward_ceiling_bounds v.numericType Q c hfrac
            hr_lo hr_hi hre_lo hre_hi hc hc0
          have hpos : (0 : ℚ) ≤ (10 : ℚ) ^ c.exponent := by positivity
          linarith
      linarith [hc_le, hQup]

/-- **Empty-branch shares have `≤16` significant digits.** The 16-digit fractional
`amount` scaled by `10^scale` and floored to `int64` keeps `≤16` significant digits:
`amount.mValue < 10^16` and the truncation only appends trailing zeros (`P ≥ 0`) or
shrinks below `10^16` (`P < 0`). -/
lemma empty_shares_sigform (v : Vault) (amount shares : STAmount)
    (hac : amount.IOUCanonical) (hscale : v.scale.toNat ≤ 18)
    (hmz : v.assetsTotal.mantissa_ = 0)
    (hshnz : shares.isZero = false)
    (hshares : assetsToSharesDeposit v amount = .ok shares) :
    shares.mIsNegative = false ∧
      ∃ s t : ℕ, shares.mValue.toNat = s * 10 ^ t ∧ s < 10 ^ 16 := by
  have hshmv : shares.mValue ≠ 0 := ne_of_beq_false (show (shares.mValue == 0) = false from hshnz)
  have hshmv' : shares.mValue.toNat ≠ 0 := fun h => hshmv (by rw [← UInt64.toNat_inj]; simpa using h)
  unfold assetsToSharesDeposit at hshares
  rw [if_pos hmz] at hshares
  obtain ⟨n1, hn1, hshares⟩ := bind_ok_peel _ _ _ hshares
  obtain ⟨n2, hn2, hshares⟩ := bind_ok_peel _ _ _ hshares
  obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hshares
  have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
  rw [hsh'] at hsh
  set P : ℤ := amount.exponent + (v.scale.toNat : ℤ) with hPdef
  have hoff_lo : (-96 : ℤ) ≤ amount.exponent := hac.exp_lo
  have hoff_hi : amount.exponent ≤ 80 := hac.exp_hi
  have hmin : minExponent = -32768 := rfl
  have hmax : maxExponent = 32768 := rfl
  have hM3 : (amount.mValue * 10 * 10 * 10).toNat = amount.mValue.toNat * 1000 :=
    m_mul_thousand_no_overflow hac.mant_hi
  have hn1_dn : doNormalize false amount.mValue P largeRange.min largeRange.max .to_nearest
      = .ok n1 := hn1
  have hlarge := doNormalize_large_16digit false amount.mValue P .to_nearest hac.mant_lo hac.mant_hi
    (by show minExponent + 3 ≤ P; rw [hPdef]; omega)
    (by show P - 3 < maxExponent; rw [hPdef]; omega)
  have hn1eq : n1 = ⟨false, amount.mValue * 10 * 10 * 10, P - 3⟩ :=
    Except.ok.inj (hn1_dn.symm.trans hlarge)
  have hn1norm : n1.isNormalized := by
    rw [hn1eq]; right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show largeRange.min ≤ amount.mValue * 10 * 10 * 10
      rw [UInt64.le_iff_toNat_le, largeRange_min_val, hM3]; have := hac.mant_lo; omega
    · show amount.mValue * 10 * 10 * 10 ≤ largeRange.max
      rw [UInt64.le_iff_toNat_le, largeRange_max_val, hM3]; have := hac.mant_hi; omega
    · right; rw [hM3]; omega
    · show minExponent ≤ P - 3; rw [hPdef]; omega
    · show P - 3 ≤ maxExponent; rw [hPdef]; omega
  have hn1neg : n1.negative_ = false := by rw [hn1eq]
  obtain ⟨hn2val, hn2normfn⟩ := Number.truncate_floor n1 n2 hn1norm hn1neg hn2
  have h1000 : (10 : ℚ) ^ (P - 3) * 1000 = (10 : ℚ) ^ P := by
    rw [show (1000 : ℚ) = (10 : ℚ) ^ (3 : ℤ) from by norm_num,
        ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    norm_num
  have hn1val : n1.toRat = (amount.mValue.toNat : ℚ) * (10 : ℚ) ^ P := by
    rw [hn1eq, Number.toRat_of_nonneg _ rfl]
    show ((amount.mValue * 10 * 10 * 10).toNat : ℚ) * (10 : ℚ) ^ (P - 3)
      = (amount.mValue.toNat : ℚ) * (10 : ℚ) ^ P
    rw [hM3]; push_cast; rw [← h1000]; ring
  have hn2m : n2.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hshmv
  have hn2norm : n2.isNormalized := hn2normfn hn2m
  have hshval : shares.toRat = n2.toRat :=
    STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide) hn2norm
      (by rw [hn2val]; exact Rat.den_intCast _) hsh
  obtain ⟨hshc, hshnt⟩ :=
    STAmount.ofNumber_integral_canonical .int64 n2 .to_nearest shares (by decide) hsh
  have hoff0 : shares.mOffset = 0 := hshc.offset_zero
  have hn1nn : 0 ≤ n1.toRat := by rw [hn1val]; positivity
  have hshnn : 0 ≤ shares.toRat := by
    rw [hshval, hn2val]; exact_mod_cast Int.floor_nonneg.mpr hn1nn
  have hshneg : shares.mIsNegative = false := by
    by_contra h; rw [Bool.not_eq_false] at h
    rw [STAmount.toRat_of_neg shares h] at hshnn
    have hp : 0 < (shares.mValue.toNat : ℚ) * (10 : ℚ) ^ shares.mOffset :=
      mul_pos (by exact_mod_cast (show 0 < shares.mValue.toNat by omega)) (by positivity)
    linarith
  refine ⟨hshneg, ?_⟩
  have hshvaln : (shares.mValue.toNat : ℚ) = shares.toRat := by
    rw [STAmount.toRat_of_nonneg shares hshneg, hoff0]; norm_num
  have hshint : (shares.mValue.toNat : ℤ) = ⌊(amount.mValue.toNat : ℚ) * (10 : ℚ) ^ P⌋ := by
    have hq : (shares.mValue.toNat : ℚ) = (⌊(amount.mValue.toNat : ℚ) * (10 : ℚ) ^ P⌋ : ℚ) := by
      rw [hshvaln, hshval, hn2val, hn1val]
    exact_mod_cast hq
  obtain ⟨s, t, hst, hslt⟩ := floor_nat_mul_zpow_sigform amount.mValue.toNat P hac.mant_hi
  exact ⟨s, t, by rw [← hst]; omega, hslt⟩

/-- **Empty-vault fractional charge is exact.** On a first deposit into an empty IOU
vault the issued `shares` come from `assetsToSharesDeposit`'s empty branch, which scales
the 16-significant-digit rounded `amount` by `10^scale` (`scale ≤ 18`), so `shares` keeps
at most 16 significant digits (`empty_shares_sigform`). The charge
`checked .fractional shares.mantissa (shares.exponent - scale)` then renormalizes losslessly
(`checked_frac_sigdigits_exact`), reproducing the ideal `shares / 10^scale`. -/
lemma empty_frac_charge_exact (v : Vault) (amount shares c : STAmount)
    (hintf : v.numericType.isIntegral = false)
    (hmz : v.assetsTotal.mantissa_ = 0)
    (hamtcanon : amount.Canonical)
    (hamtfrac : amount.mNumericType = .fractional)
    (hshares : assetsToSharesDeposit v amount = .ok shares)
    (hshnz : shares.isZero = false)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    c.toRat = v.idealChargeDeposit shares.toRat := by
  have hamtint : amount.integral = false := by
    unfold STAmount.integral; rw [hamtfrac]; decide
  have hac : amount.IOUCanonical := hamtcanon.2 hamtint
  obtain ⟨hshneg, s, t, hst, hslt⟩ :=
    empty_shares_sigform v amount shares hac v.wf.scale_le hmz hshnz hshares
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hshares
  have hshmv : shares.mValue ≠ 0 := ne_of_beq_false (show (shares.mValue == 0) = false from hshnz)
  have hshmv' : shares.mValue.toNat ≠ 0 := fun h => hshmv (by rw [← UInt64.toNat_inj]; simpa using h)
  have hfit : shares.mValue.toNat < 2 ^ 63 := by
    have hr := hshc.in_range; rw [hshnt] at hr
    have hm : NumericType.int64.maxValue.toNat = 9223372036854775807 := by decide
    omega
  have hvfrac : v.numericType = .fractional := by
    cases hnt : v.numericType with
    | fractional => rfl
    | integral _ _ _ _ => rw [hnt] at hintf; simp [NumericType.isIntegral] at hintf
  unfold sharesToAssetsDeposit at hsad
  rw [if_pos hmz] at hsad
  obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hc' : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  have hexp0 : shares.exponent = 0 := hshc.offset_zero
  rw [hc', hvfrac, show shares.mantissa = shares.mValue from rfl, hexp0] at hcx
  have hcval : c.toRat = (shares.mValue.toNat : ℚ) * (10 : ℚ) ^ ((0 : ℤ) - (v.scale.toNat : ℤ)) := by
    apply STAmount.checked_frac_sigdigits_exact shares.mValue ((0 : ℤ) - (v.scale.toNat : ℤ))
      .to_nearest c s t hst hslt hshmv hfit
    · show (-18 : ℤ) ≤ (0 : ℤ) - (v.scale.toNat : ℤ); have h18 := v.wf.scale_le; omega
    · show (0 : ℤ) - (v.scale.toNat : ℤ) ≤ 0; omega
    · exact hcx
  rw [hcval]
  unfold RawVault.idealChargeDeposit
  have hA0 : v.toExact.assetsTotal = 0 := Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal hmz
  rw [if_pos hA0]
  have hsheq : shares.toRat = (shares.mValue.toNat : ℚ) := by
    rw [STAmount.toRat_of_nonneg shares hshneg, hshc.offset_zero]; norm_num
  rw [hsheq, show (0 : ℤ) - (v.scale.toNat : ℤ) = -(v.scale.toNat : ℤ) from by ring,
      zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- **Proof body of `Vault.deposit_charge`.** The exchange charge is the raw
`computeDeposit`/`sharesToAssetsDeposit` output. The source then clamps that output
at the posterior-total scale before returning it and updating state. Accordingly,
the final-return bounds carry the exact clamp-rounding correction
`rawAssetDeposited.toRat - r.amountDeposit'.toRat`; no raw/final identity is assumed. -/
theorem Vault.deposit_charge_proof (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    ∃ rawAssetDeposited : STAmount,
      clampToSumExponent v.assetsTotal rawAssetDeposited = .ok r.amountDeposit' ∧
      rawAssetDeposited.toRat ≤ amountDeposit.toRat ∧
      (rawAssetDeposited.isZero = false →
        v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) ≤
          r.amountDeposit'.toRat +
            (rawAssetDeposited.toRat - r.amountDeposit'.toRat)) ∧
      (rawAssetDeposited.isZero = true →
        v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) <
          if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) ∧
      (rawAssetDeposited.isZero = false →
        r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
          v.idealChargeDeposit r.sharesIssued.toRat * depositε +
            2 * (10 : ℚ) ^ rawAssetDeposited.exponent -
              (rawAssetDeposited.toRat - r.amountDeposit'.toRat)) := by
  obtain ⟨amount, rawAssetDeposited, assetDeposited, sharesCreated, cN, sN, at', av', st',
    hround, hanz, _, _, _, hcd, _, _, _, _, _, _, hamt, hshr, _⟩ :=
    Vault.deposit_success_reduces v amountDeposit false r hok herr
  obtain ⟨shares, hats, hsz, hsad, hgt, hsheq⟩ :=
    computeDeposit_success_reduces v amount rawAssetDeposited sharesCreated (hcd rfl).1
  have hamt_canon : amount.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit amount v.assetsTotal hcanon hround
      with h | h
    · exact h
    · rw [h] at hanz; exact absurd hanz (by decide)
  have hamt_nn : 0 ≤ amount.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit amount v.assetsTotal hcanon (le_of_lt hpos) hround
  have hamt_mv : amount.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hanz; exact hanz)
  have hamt_pos : 0 < amount.toRat :=
    lt_of_le_of_ne hamt_nn (Ne.symm (fun h => hamt_mv ((STAmount.toRat_eq_zero_iff amount).mp h)))
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v amount shares hamt_canon hamt_pos hats hsz
  have hcr : r.amountDeposit' = assetDeposited := hamt
  have hsr : r.sharesIssued = shares := by rw [hshr]; exact hsheq
  have hraw_le : rawAssetDeposited.toRat ≤ amountDeposit.toRat := by
    have hle_amt : amount.toRat ≤ amountDeposit.toRat :=
      RawVault.roundToVaultExponent_le amountDeposit amount v.assetsTotal hcanon (le_of_lt hpos) hround
    by_cases hc0 : rawAssetDeposited.mValue = 0
    · rw [(STAmount.toRat_eq_zero_iff _).mpr hc0]; linarith [hpos]
    · have hexact : rawAssetDeposited.ExactCanonical := by
        rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares rawAssetDeposited hshc hshnt hsad
          with h | h0
        · exact h
        · exact absurd h0 hc0
      have hcmp_ab : STAmount.areComparable rawAssetDeposited amount = true := by
        rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
        split at hgt
        · exact absurd hgt (by simp)
        · rename_i hcond; rw [STAmount.areComparable_comm]; simpa using hcond
      have hcmpF : STAmount.CmpFaithful rawAssetDeposited amount :=
        STAmount.CmpFaithful.ofExactCanonical rawAssetDeposited amount hexact
          (STAmount.Canonical.exactCanonical amount hamt_canon) hcmp_ab
          (fun h => absurd h hc0) (fun h => absurd h hamt_mv)
      have hle := computeDeposit_success_charge_le v amount rawAssetDeposited sharesCreated hcmpF (hcd rfl).1
      exact hle.trans hle_amt
  -- All charge/exchange facts below are deliberately facts about the raw result.
  have hcty : rawAssetDeposited.mNumericType = v.numericType :=
    sharesToAssetsDeposit_mNumericType v shares rawAssetDeposited hsad
  have hcmp_ty : STAmount.areComparable rawAssetDeposited amount = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; rw [STAmount.areComparable_comm]; simpa using hcond
  have hamt_ty : amount.mNumericType = v.numericType := by
    have hb := hcmp_ty; unfold STAmount.areComparable at hb
    exact (beq_iff_eq.mp hb).symm.trans hcty
  have hfrac_exact : v.assetsTotal.mantissa_ = 0 → v.numericType.isIntegral = false →
      rawAssetDeposited.toRat = v.idealChargeDeposit shares.toRat :=
    fun hmz' hintf =>
      empty_frac_charge_exact v amount shares rawAssetDeposited hintf hmz' hamt_canon
        (by rw [hamt_ty]
            cases hnt : v.numericType with
            | fractional => rfl
            | integral _ _ _ _ => rw [hnt] at hintf; simp [NumericType.isIntegral] at hintf)
        hats hsz hsad
  obtain ⟨_, hcore_lower, hcore_zero, hcore_upper⟩ :=
    sharesToAssetsDeposit_charge_bound v shares rawAssetDeposited hshc hshnt hshpos
      hfrac_exact hsad
  refine ⟨rawAssetDeposited, ?_, hraw_le, ?_, ?_, ?_⟩
  · rw [hcr]
    exact (hcd rfl).2.1
  · intro hraw_nz
    have hraw : v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) ≤
        rawAssetDeposited.toRat := by
      simpa only [hsr] using hcore_lower hraw_nz
    linarith
  · intro hraw_z
    rw [hsr]
    exact hcore_zero hraw_z
  · intro hraw_nz
    have hraw := hcore_upper hraw_nz
    rw [hcr, hsr]
    linarith

end XRPL.Model.SingleAssetVault
