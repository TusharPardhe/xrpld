import XRPL.Properties.Vault.Common.PricingMono
import XRPL.Properties.Vault.Common.WithdrawClampMono
import XRPL.Properties.Vault.Common.WithdrawPostSumMono
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangePos
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow
import XRPL.Properties.Protocol.Number.Div.Common.Decompose

/-! # Withdraw payout monotonicity

`ofNumber .downward` is the exact floor to the STAmount grid, hence monotone. The
withdraw payout is `ofNumber .downward ((nav2 * shares.toNumber) / sharesTotal)`,
so it is monotone in the shares amount.

The larger payout may floor to zero. Covering it needs the pre-floor `Number`
quotient `aN₂` to be nonzero so the pricing chain (`Number.mul_div_num_mono`) and
the downward floor (`ofNumber_downward_toRat_mono`) apply. A nonzero smaller payout
anchors the whole run-1 chain at or above the smallest positive STAmount `10^-81`
(the downward floor of a nonzero source is a nonzero canonical amount, so at least
`10^-81`), which is astronomically above the `Number` underflow threshold
`σ = 10^18 · 10^minExponent = 10^-32750`. Pricing monotonicity carries that anchor
to run 2, so both the product and the quotient stay above `σ`
(`operator_mul/div_underflow_truth_small`) and never flush to zero. -/

namespace XRPL.Model.Protocol

open XRPL.Model.SingleAssetVault

/-- The `Number` underflow threshold `σ = 10^18 · 10^minExponent` is far below the
smallest positive STAmount `10^-81`. -/
lemma sigma_le_min_stamount :
    (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ (10 : ℚ) ^ (-82 : ℤ) := by
  rw [show ((10 : ℚ) ^ (18 : ℕ)) = (10 : ℚ) ^ ((18 : ℕ) : ℤ) from (zpow_natCast 10 18).symm,
      ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
  exact zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; omega)

/-- **Exact 16-digit floor** for the fractional `.downward` conversion of a positive
normalized `Number`: `result = m · 10^e` with `m ∈ [10^15, 10^16)` and
`m · 10^e ≤ n < (m+1) · 10^e`. -/
lemma ofNumber_downward_floor_frac (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber .fractional n .downward = .ok result) (hres : result.mValue ≠ 0) :
    ∃ (m e : ℤ), result.toRat = (m : ℚ) * 10 ^ e ∧ (10 : ℤ) ^ 15 ≤ m ∧ m < 10 ^ 16 ∧
      (m : ℚ) * 10 ^ e ≤ n.toRat ∧ n.toRat < ((m : ℚ) + 1) * 10 ^ e ∧ (-96 : ℤ) ≤ e := by
  have hn_ne : n.mantissa_ ≠ 0 :=
    STAmount.ofNumber_iou_mantissa_ne_zero .fractional n .downward result rfl hok hres
  obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
  have hexp_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
    · exact hlo
  have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
    STAmount.ofNumber_iou_success_exp_range n .downward result hlo19 hhi19 hexp_lo hok hres
  obtain ⟨mant, exp, hnorm', hval, _hexp_res, hcast, hm_lo, hm_hi, he_lo, _he_hi⟩ :=
    STAmount.ofNumber_iou_snap_pos .fractional n .downward result rfl hneg
      hlo19 hhi19 hexp_lo hexp_hi hok hres
  obtain ⟨hfloor_eq, hexp_eq⟩ :=
    normalizeToRange_16_floor_pos n mant exp .downward (Or.inl rfl) hneg hlo19 hhi19
      (by omega) hexp_hi hnorm'
  set M : ℕ := n.mantissa_.toNat with hM
  set e : ℤ := n.exponent_ with he
  have hpow_exp : (10 : ℚ) ^ exp = 10 ^ e * 1000 := by
    rw [hexp_eq]; rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
  have hpow_e_pos : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  have hntoRat : n.toRat = (M : ℚ) * 10 ^ e := by
    rw [hM, he, Number.toRat_of_nonneg n (by simpa using hneg)]
  -- mant.toInt = M / 1000
  have hmeq : (mant.toInt : ℚ) = ((M / 1000 : ℕ) : ℚ) := by
    have hpow_pos : (0 : ℚ) < (10 : ℚ) ^ exp := zpow_pos (by norm_num) _
    have h1 : (mant.toInt : ℚ) * 10 ^ exp = ((M / 1000 : ℕ) : ℚ) * 10 ^ exp := by
      rw [hfloor_eq, hexp_eq, hM]
    exact mul_right_cancel₀ (ne_of_gt hpow_pos) h1
  have hdiv_le : (M / 1000) * 1000 ≤ M := Nat.div_mul_le_self M 1000
  have hdiv_lt : M < (M / 1000) * 1000 + 1000 := by omega
  have hdiv_le_q : ((M / 1000 : ℕ) : ℚ) * 1000 ≤ (M : ℚ) := by exact_mod_cast hdiv_le
  have hdiv_lt_q : (M : ℚ) < ((M / 1000 : ℕ) : ℚ) * 1000 + 1000 := by exact_mod_cast hdiv_lt
  have hcastZ : mant.toInt = (mant.toUInt64.toNat : ℤ) := by exact_mod_cast hcast
  refine ⟨mant.toInt, exp, hval, ?_, ?_, ?_, ?_, he_lo⟩
  · rw [hcastZ]; exact_mod_cast hm_lo
  · rw [hcastZ]; exact_mod_cast hm_hi
  · rw [hmeq, hntoRat, hpow_exp]
    have : ((M / 1000 : ℕ) : ℚ) * (10 ^ e * 1000) = (((M / 1000 : ℕ) : ℚ) * 1000) * 10 ^ e := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hdiv_le_q (le_of_lt hpow_e_pos)
  · rw [hmeq, hntoRat, hpow_exp]
    have hrw : (((M / 1000 : ℕ) : ℚ) + 1) * (10 ^ e * 1000)
        = (((M / 1000 : ℕ) : ℚ) * 1000 + 1000) * 10 ^ e := by ring
    rw [hrw]
    exact mul_lt_mul_of_pos_right hdiv_lt_q hpow_e_pos

/-- **Exact integer floor** for the integral `.downward` conversion of a positive
normalized `Number`: `result = m` (an integer) with `m ≤ n < m+1`. -/
lemma ofNumber_downward_floor_int (nt : NumericType) (n : Number) (result : STAmount)
    (hint : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .downward = .ok result) :
    ∃ (m : ℤ), result.toRat = (m : ℚ) ∧ (m : ℚ) ≤ n.toRat ∧ n.toRat < (m : ℚ) + 1 ∧ 0 ≤ m := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
  cases hr : n.to_rep .downward with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n .downward intValue hneg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat := toUInt64_toNat_le_maxRep intValue hnn hle
    have hres_val : result.toRat = (intValue.toInt : ℚ) := by
      have hexact := STAmount.canonicalize_integral_toRat
        (STAmount.unchecked nt intValue.toUInt64 0 false) result .downward
        (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
        hval hok
      rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
      show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
      rw [toUInt64_toNat_of_nonneg intValue hnn]
    obtain ⟨hfl_le, hfl_lt⟩ := Number.to_rep_downward_floor n intValue hn hneg hr
    exact ⟨intValue.toInt, hres_val, hfl_le, hfl_lt, by exact_mod_cast hnn⟩

/-- Zero `mValue` gives zero value. -/
private lemma toRat_zero_of_mValue (a : STAmount) (h : a.mValue = 0) : a.toRat = 0 := by
  rw [STAmount.toRat_signed, h]; simp

/-- **`ofNumber .downward` is monotone.** The exact floor to the STAmount grid never
inverts: a larger positive normalized input never floors to a smaller amount. -/
theorem ofNumber_downward_toRat_mono (nt : NumericType) (n₁ n₂ : Number)
    (result₁ result₂ : STAmount)
    (hn₁ : n₁.isNormalized) (hneg₁ : n₁.negative_ = false) (_hnz₁ : n₁.mantissa_ ≠ 0)
    (hn₂ : n₂.isNormalized) (hneg₂ : n₂.negative_ = false) (hnz₂ : n₂.mantissa_ ≠ 0)
    (hok₁ : STAmount.ofNumber nt n₁ .downward = .ok result₁)
    (hok₂ : STAmount.ofNumber nt n₂ .downward = .ok result₂)
    (hle : n₁.toRat ≤ n₂.toRat) : result₁.toRat ≤ result₂.toRat := by
  have hr2nn : 0 ≤ result₂.toRat := by
    by_cases h : result₂.mValue = 0
    · rw [toRat_zero_of_mValue result₂ h]
    · exact (STAmount.ofNumber_downward_floor_bounds nt n₂ result₂ hn₂ hneg₂ hok₂ h).2.2
  by_cases hr₁ : result₁.mValue = 0
  · rw [toRat_zero_of_mValue result₁ hr₁]; exact hr2nn
  · by_cases hnti : nt.isIntegral = true
    · -- integral: floor at scale 0
      obtain ⟨m₁, hv₁, hle₁, _, hm₁nn⟩ :=
        ofNumber_downward_floor_int nt n₁ result₁ hnti hn₁ hneg₁ hok₁
      have hm₁1 : (1 : ℚ) ≤ (m₁ : ℚ) := by
        have hne : (m₁ : ℚ) ≠ 0 := by rw [← hv₁]; exact STAmount.toRat_ne_zero result₁ hr₁
        have hm₁ne : m₁ ≠ 0 := by exact_mod_cast hne
        have : (0 : ℤ) < m₁ := lt_of_le_of_ne hm₁nn (Ne.symm hm₁ne)
        exact_mod_cast this
      by_cases hr₂ : result₂.mValue = 0
      · exfalso
        have hn₂lt := STAmount.ofNumber_integral_zero_floor nt n₂ result₂ hnti hn₂ hneg₂ hok₂ hr₂
        linarith [hle₁, hle]
      · obtain ⟨m₂, hv₂, _, hlt₂, _⟩ :=
          ofNumber_downward_floor_int nt n₂ result₂ hnti hn₂ hneg₂ hok₂
        rw [hv₁, hv₂]
        have hlt : (m₁ : ℚ) < (m₂ : ℚ) + 1 := by linarith [hle₁, hle, hlt₂]
        have : m₁ < m₂ + 1 := by exact_mod_cast hlt
        exact_mod_cast (by omega : m₁ ≤ m₂)
    · -- fractional: exact 16-digit floor
      have hnti' : nt.isIntegral = false := by
        cases h : nt.isIntegral with
        | false => rfl
        | true => exact absurd h hnti
      have hntf : nt = .fractional := by cases nt with | fractional => rfl | integral => simp [NumericType.isIntegral] at hnti'
      subst hntf
      obtain ⟨m₁, e₁, hv₁, hml₁, hmh₁, hle₁, _, he₁⟩ :=
        ofNumber_downward_floor_frac n₁ result₁ hn₁ hneg₁ hok₁ hr₁
      by_cases hr₂ : result₂.mValue = 0
      · exfalso
        have hn₂lt := STAmount.ofNumber_fractional_zero_below_min .fractional n₂ result₂
          (by decide) hn₂ hneg₂ hnz₂ hok₂ hr₂
        have hp₁ : (0 : ℚ) < 10 ^ e₁ := zpow_pos (by norm_num) _
        have hml₁q : (10 : ℚ) ^ (15 : ℤ) ≤ (m₁ : ℚ) := by
          have : ((10 : ℤ) ^ 15 : ℤ) ≤ m₁ := hml₁
          have hcast : ((10 : ℤ) ^ 15 : ℚ) = (10 : ℚ) ^ (15 : ℤ) := by push_cast; norm_num
          rw [← hcast]; exact_mod_cast this
        -- result₁ = m₁·10^e₁ ≥ 10^15·10^e₁ ≥ 10^15·10^(-96) = 10^(-81)
        have hpow_ge : (10 : ℚ) ^ (-81 : ℤ) ≤ (m₁ : ℚ) * 10 ^ e₁ := by
          have h1 : (10 : ℚ) ^ (15 : ℤ) * 10 ^ (-96 : ℤ) ≤ (m₁ : ℚ) * 10 ^ e₁ := by
            apply mul_le_mul hml₁q (zpow_le_zpow_right₀ (by norm_num) he₁) (by positivity) (by positivity)
          have h2 : (10 : ℚ) ^ (15 : ℤ) * 10 ^ (-96 : ℤ) = 10 ^ (-81 : ℤ) := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
          linarith [h1, h2 ▸ h1]
        linarith [hle₁, hle, hn₂lt, hpow_ge]
      · obtain ⟨m₂, e₂, hv₂, hml₂, hmh₂, hle₂, hlt₂, _⟩ :=
          ofNumber_downward_floor_frac n₂ result₂ hn₂ hneg₂ hok₂ hr₂
        rw [hv₁, hv₂]
        have hp₁ : (0 : ℚ) < 10 ^ e₁ := zpow_pos (by norm_num) _
        have hp₂ : (0 : ℚ) < 10 ^ e₂ := zpow_pos (by norm_num) _
        have hc15 : ((10 : ℤ) ^ 15 : ℚ) = (10 : ℚ) ^ (15 : ℤ) := by push_cast; norm_num
        have hc16 : ((10 : ℤ) ^ 16 : ℚ) = (10 : ℚ) ^ (16 : ℤ) := by push_cast; norm_num
        have hml₁q : (10 : ℚ) ^ (15 : ℤ) ≤ (m₁ : ℚ) := by rw [← hc15]; exact_mod_cast hml₁
        have hml₂q : (10 : ℚ) ^ (15 : ℤ) ≤ (m₂ : ℚ) := by rw [← hc15]; exact_mod_cast hml₂
        have hmh₁q : (m₁ : ℚ) < 10 ^ (16 : ℤ) := by rw [← hc16]; exact_mod_cast hmh₁
        have hmh₂q : (m₂ : ℚ) < 10 ^ (16 : ℤ) := by rw [← hc16]; exact_mod_cast hmh₂
        rcases lt_trichotomy e₁ e₂ with he | he | he
        · -- e₁ < e₂: magnitude bands separate
          have hstep : (10 : ℚ) ^ (16 : ℤ) * 10 ^ e₁ ≤ 10 ^ (15 : ℤ) * 10 ^ e₂ := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
            exact zpow_le_zpow_right₀ (by norm_num) (by omega)
          apply le_of_lt
          calc (m₁ : ℚ) * 10 ^ e₁ < 10 ^ (16 : ℤ) * 10 ^ e₁ := mul_lt_mul_of_pos_right hmh₁q hp₁
            _ ≤ 10 ^ (15 : ℤ) * 10 ^ e₂ := hstep
            _ ≤ (m₂ : ℚ) * 10 ^ e₂ := mul_le_mul_of_nonneg_right hml₂q (le_of_lt hp₂)
        · subst he
          have hlt : (m₁ : ℚ) < (m₂ : ℚ) + 1 := by
            have := lt_of_le_of_lt (le_trans hle₁ hle) hlt₂
            have hpp : (0:ℚ) < 10^e₁ := hp₁
            nlinarith [this, hpp]
          have hm₁z : m₁ < m₂ + 1 := by exact_mod_cast hlt
          have : (m₁ : ℚ) ≤ (m₂ : ℚ) := by exact_mod_cast (by omega : m₁ ≤ m₂)
          exact mul_le_mul_of_nonneg_right this (le_of_lt hp₁)
        · exfalso
          have hstep : (10 : ℚ) ^ (16 : ℤ) * 10 ^ e₂ ≤ 10 ^ (15 : ℤ) * 10 ^ e₁ := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
            exact zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hr1_ge : (10 : ℚ) ^ (15 : ℤ) * 10 ^ e₁ ≤ (m₁ : ℚ) * 10 ^ e₁ :=
            mul_le_mul_of_nonneg_right hml₁q (le_of_lt hp₁)
          have hn₂_lt : n₂.toRat < 10 ^ (16 : ℤ) * 10 ^ e₂ := by
            refine lt_of_lt_of_le hlt₂ ?_
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hp₂)
            rw [← hc16]; exact_mod_cast (show m₂ + 1 ≤ (10 : ℤ) ^ 16 by omega)
          linarith [hle₁, hle, hn₂_lt, hstep, hr1_ge]

/-- **A nonzero downward `ofNumber` came from a source at least `10^-81`.** The floor
of `n` is a nonzero canonical STAmount, hence at least the grid minimum `10^-81`, and
the floor never exceeds the source. This anchors the pricing chain far above the
`Number` underflow threshold. -/
lemma ofNumber_downward_source_ge_min (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hres : result.isZero = false) :
    (10 : ℚ) ^ (-81 : ℤ) ≤ n.toRat := by
  have hmv : result.mValue ≠ 0 := ne_of_beq_false hres
  by_cases hint : nt.isIntegral = true
  · obtain ⟨m, hval, hle, _, hm_nn⟩ := ofNumber_downward_floor_int nt n result hint hn hneg hok
    have hm1 : (1 : ℚ) ≤ (m : ℚ) := by
      have hrne : result.toRat ≠ 0 := STAmount.toRat_ne_zero result hmv
      rw [hval] at hrne
      have hmne : m ≠ 0 := by exact_mod_cast hrne
      exact_mod_cast lt_of_le_of_ne hm_nn (Ne.symm hmne)
    have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := by
      rw [show (1 : ℚ) = (10 : ℚ) ^ (0 : ℤ) from by norm_num]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [hle, hm1, h81]
  · have hntf : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral _ _ _ _ => simp [NumericType.isIntegral] at hint
    subst hntf
    obtain ⟨m, e, hval, hml, _, hle, _, he_lo⟩ := ofNumber_downward_floor_frac n result hn hneg hok hmv
    have hp : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
    have hmq : (10 : ℚ) ^ (15 : ℤ) ≤ (m : ℚ) := by
      have hc : ((10 : ℤ) ^ 15 : ℚ) = (10 : ℚ) ^ (15 : ℤ) := by push_cast; norm_num
      rw [← hc]; exact_mod_cast hml
    have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ (m : ℚ) * 10 ^ e := by
      have hstep : (10 : ℚ) ^ (15 : ℤ) * 10 ^ (-96 : ℤ) ≤ (m : ℚ) * 10 ^ e := by
        apply mul_le_mul hmq (zpow_le_zpow_right₀ (by norm_num) he_lo) (by positivity) (by positivity)
      have heq : (10 : ℚ) ^ (15 : ℤ) * 10 ^ (-96 : ℤ) = 10 ^ (-81 : ℤ) := by
        rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
      linarith [heq ▸ hstep]
    linarith [hle, h81]

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Full nonzero-payout pricing chain of `sharesToAssetsWithdraw` with every stage's
normalization / nonzero-mantissa / positivity fact. -/
lemma withdraw_chain_facts (v : Vault) (waiveUnrealizedLoss : Bool)
    (shares assets : STAmount) (hc : shares.Canonical) (hnn : 0 ≤ shares.toRat)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets)
    (hnz : assets.isZero = false) :
    ∃ (nav2 sn NV aN : Number),
      nav2.isNormalized ∧ nav2.mantissa_ ≠ 0 ∧ 0 < nav2.toRat ∧
      nav2.toRat = (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) ∧
      shares.toNumber .to_nearest = .ok sn ∧ sn.toRat = shares.toRat ∧
      sn.isNormalized ∧ sn.mantissa_ ≠ 0 ∧ 0 < sn.toRat ∧
      v.sharesTotal.mantissa_ ≠ 0 ∧ 0 < v.sharesTotal.toRat ∧
      nav2.operator_mul sn .to_nearest = .ok NV ∧ NV.isNormalized ∧ NV.mantissa_ ≠ 0 ∧
      NV.operator_div v.sharesTotal .to_nearest = .ok aN ∧ aN.isNormalized ∧ aN.mantissa_ ≠ 0 ∧
      0 < aN.toRat ∧ STAmount.ofNumber v.numericType aN .downward = .ok assets := by
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
  have hnav_nonneg : 0 ≤ (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) := by
    cases waiveUnrealizedLoss with
    | false => rw [if_neg (by decide)]; exact v.exact.withdraw_nav_nonneg
    | true =>
      rw [if_pos rfl]; show 0 ≤ v.depositNav; unfold RawVault.depositNav
      exact v.exact.assetsTotal_nonneg
  rcases hcase with ⟨_, hzero⟩ | ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · rw [hzero, STAmount.zero_isZero] at hnz; exact absurd hnz (by decide)
  · have hres_ne : assets.mValue ≠ 0 := ne_of_beq_false hnz
    have hnav2_ne0 : nav2.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero nav2 hnav2m
    have hnav_pos : 0 < nav2.toRat :=
      lt_of_le_of_ne (hnav2_val.symm ▸ hnav_nonneg) (Ne.symm hnav2_ne0)
    obtain ⟨sn0, hsn0ok, hsn0val, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsn_eq : sn0 = sharesNumber := by rw [hsn0ok] at hsn; exact Except.ok.inj hsn
    have hsnnorm : sharesNumber.isNormalized := by rw [← hsn_eq]; exact hsn0norm
    have hsnval : sharesNumber.toRat = shares.toRat := by rw [← hsn_eq]; exact hsn0val
    have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
      operator_div_divisor_ne_zero NAVShares v.sharesTotal assetsNumber .to_nearest
        v.wf.sharesTotal_norm hdiv
    have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
      (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.sharesTotal hSTm))
    have hanm : assetsNumber.mantissa_ ≠ 0 :=
      STAmount.ofNumber_source_ne_zero v.numericType assetsNumber .downward assets hof hres_ne
    have hNAVm : NAVShares.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hdiv hanm
    obtain ⟨_, hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
    have hsnpos : 0 < sharesNumber.toRat :=
      lt_of_le_of_ne (hsnval ▸ hnn) (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero sharesNumber hsn_m))
    have hNAVnorm : NAVShares.isNormalized :=
      operator_mul_result_isNormalized nav2 sharesNumber NAVShares .to_nearest
        hnav2norm hsnnorm hnav2m hsn_m hmul hNAVm
    have hANnorm : assetsNumber.isNormalized :=
      operator_div_result_isNormalized NAVShares v.sharesTotal assetsNumber .to_nearest
        hNAVnorm v.wf.sharesTotal_norm hNAVm hSTm hdiv hanm
    have hNAVpos : 0 < NAVShares.toRat := by
      have hb : |NAVShares.toRat - nav2.toRat * sharesNumber.toRat|
          ≤ |nav2.toRat * sharesNumber.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) :=
        operator_mul_rounds_to_nearest nav2 sharesNumber NAVShares hnav2norm hsnnorm hmul hNAVm
      rw [abs_of_pos (mul_pos hnav_pos hsnpos)] at hb
      have hab := abs_le.mp hb
      nlinarith [mul_pos hnav_pos hsnpos]
    have hANpos : 0 < assetsNumber.toRat := by
      have hqp : 0 < NAVShares.toRat / v.sharesTotal.toRat := div_pos hNAVpos hSTpos
      have hb : |assetsNumber.toRat - NAVShares.toRat / v.sharesTotal.toRat|
          ≤ |NAVShares.toRat / v.sharesTotal.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) :=
        operator_div_rounds_to_nearest NAVShares v.sharesTotal assetsNumber
          hNAVnorm v.wf.sharesTotal_norm hdiv hanm
      rw [abs_of_pos hqp] at hb
      have hab := abs_le.mp hb
      nlinarith [hqp]
    exact ⟨nav2, sharesNumber, NAVShares, assetsNumber, hnav2norm, hnav2m, hnav_pos, hnav2_val,
      hsn, hsnval, hsnnorm, hsn_m, hsnpos, hSTm, hSTpos,
      hmul, hNAVnorm, hNAVm, hdiv, hANnorm, hanm, hANpos, hof⟩

/-- Run reduction exposing the normalized `nav2` (with its value) and the burned
`shares.toNumber`, then either the zero-`nav` early exit or the raw
`mul`/`div`/`ofNumber` pricing chain (no nonzero-mantissa facts). Companion to
`withdraw_chain_facts` for a run whose payout may floor to zero. -/
lemma withdraw_nav_pricing_reduces (v : Vault) (waive : Bool)
    (shares assets : STAmount) (hc : shares.Canonical) (hnav : v.WithdrawNavExact waive)
    (hok : v.sharesToAssetsWithdraw shares waive = .ok assets) :
    ∃ (nav2 sn : Number),
      nav2.isNormalized ∧ nav2.toRat = (if waive then v.depositNav else v.withdrawNav) ∧
      shares.toNumber .to_nearest = .ok sn ∧ sn.isNormalized ∧ sn.toRat = shares.toRat ∧
      ((nav2.mantissa_ = 0 ∧ assets = STAmount.zero v.numericType) ∨
       (nav2.mantissa_ ≠ 0 ∧ ∃ NV aN : Number,
         nav2.operator_mul sn .to_nearest = .ok NV ∧
         NV.operator_div v.sharesTotal .to_nearest = .ok aN ∧
         STAmount.ofNumber v.numericType aN .downward = .ok assets)) := by
  obtain ⟨nav2, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waive hok
  have hnav2facts : nav2.isNormalized ∧
      nav2.toRat = (if waive then v.depositNav else v.withdrawNav) := by
    obtain ⟨nv, he, heval⟩ := hnav
    cases waive with
    | false =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm
        v.wf.lossUnrealized_norm hsub, by rw [hval]; exact heval⟩
    | true =>
      have hval : nav2 = nv := Except.ok.inj (hsub.symm.trans he)
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub,
        by rw [hval]; exact heval⟩
  obtain ⟨hnav2norm, hnav2val⟩ := hnav2facts
  obtain ⟨sn0, hsn0ok, hsn0val, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
  refine ⟨nav2, sn0, hnav2norm, hnav2val, hsn0ok, hsn0norm, hsn0val, ?_⟩
  rcases hcase with ⟨hm0, hz⟩ | ⟨hm, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · exact Or.inl ⟨hm0, hz⟩
  · have hsn_eq : sn0 = sharesNumber := by rw [hsn0ok] at hsn; exact Except.ok.inj hsn
    subst hsn_eq
    exact Or.inr ⟨hm, NAVShares, assetsNumber, hmul, hdiv, hof⟩

set_option maxHeartbeats 1000000 in
-- high budget: full pricing-chain monotonicity plus the underflow-floor case, closed by heavy nlinarith
/-- **`sharesToAssetsWithdraw` is monotone in the shares.** The pricing chain and the
downward floor are each monotone, and the larger run's payout flooring to zero is
covered: run 1's nonzero payout anchors the exact quotient above `10^-81` (grid
minimum), astronomically above the `Number` underflow `σ = 10^-32750`, so pricing
monotonicity keeps run 2's product and quotient above `σ` and its pre-floor quotient
stays nonzero, letting the pricing- and floor-monotonicity lemmas apply. -/
lemma sharesToAssetsWithdraw_mono (v : Vault) (waiveUnrealizedLoss : Bool)
    (shares₁ shares₂ assets₁ assets₂ : STAmount)
    (hc₁ : shares₁.Canonical) (hnn₁ : 0 ≤ shares₁.toRat)
    (hc₂ : shares₂.Canonical) (hnn₂ : 0 ≤ shares₂.toRat)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok₁ : v.sharesToAssetsWithdraw shares₁ waiveUnrealizedLoss = .ok assets₁)
    (hok₂ : v.sharesToAssetsWithdraw shares₂ waiveUnrealizedLoss = .ok assets₂)
    (hle : shares₁.toRat ≤ shares₂.toRat) : assets₁.toRat ≤ assets₂.toRat := by
  -- the larger run's payout is always non-negative
  have hr2nn : 0 ≤ assets₂.toRat :=
    (Vault.sharesToAssetsWithdraw_spec v shares₂ assets₂ waiveUnrealizedLoss hnn₂ hc₂ hnav hok₂).1
  by_cases hz₁ : assets₁.isZero = true
  · have hmv : assets₁.mValue = 0 := by
      have := hz₁; unfold STAmount.isZero at this; exact beq_iff_eq.mp this
    rw [toRat_zero_of_mValue assets₁ hmv]; exact hr2nn
  have hz₁' : assets₁.isZero = false := by simpa using hz₁
  -- run 1: the full nonzero pricing chain
  obtain ⟨nav2a, sn₁, NV₁, aN₁, hnav2na, hnav2ma, hnav2pa, hnav2vala,
      hsn₁, hsnval₁, hsnn₁, hsnm₁, hsnp₁, hSTm, hSTp,
      hmul₁, hNVn₁, hNVm₁, hdiv₁, hANn₁, hANm₁, hANp₁, hof₁⟩ :=
    withdraw_chain_facts v waiveUnrealizedLoss shares₁ assets₁ hc₁ hnn₁ hnav hok₁ hz₁'
  set ST : ℚ := v.sharesTotal.toRat with hST_def
  have hST1 : 1 ≤ ST := by
    have hden : v.sharesTotal.toRat.den = 1 := v.wf.sharesTotal_int
    have heq : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      rw [← Rat.num_div_den v.sharesTotal.toRat, hden]; simp
    rw [hST_def, heq]
    have hpos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hSTp
    exact_mod_cast (by omega : (1 : ℤ) ≤ v.sharesTotal.toRat.num)
  -- anchor: aN₁ ≥ 10^-81
  have haN₁neg : aN₁.negative_ = false := Number.negative_false_of_pos aN₁ hANp₁
  have hanchor : (10 : ℚ) ^ (-81 : ℤ) ≤ aN₁.toRat :=
    ofNumber_downward_source_ge_min v.numericType aN₁ assets₁ hANn₁ haN₁neg hof₁ hz₁'
  -- run 2: nav2 + burned shares + raw pricing chain (payout may floor to zero)
  obtain ⟨nav2b, sn₂, hnav2nb, hnav2valb, hsn₂, hsnn₂, hsnval₂, hcase₂⟩ :=
    withdraw_nav_pricing_reduces v waiveUnrealizedLoss shares₂ assets₂ hc₂ hnav hok₂
  have hnav2eq : nav2a = nav2b := hnav2na.toRat_inj hnav2nb (by rw [hnav2vala, hnav2valb])
  subst hnav2eq
  have hpricing : nav2a.mantissa_ ≠ 0 ∧ ∃ NV aN : Number,
      nav2a.operator_mul sn₂ .to_nearest = .ok NV ∧
      NV.operator_div v.sharesTotal .to_nearest = .ok aN ∧
      STAmount.ofNumber v.numericType aN .downward = .ok assets₂ := by
    rcases hcase₂ with ⟨hm0, _⟩ | h
    · exact absurd hm0 hnav2ma
    · exact h
  obtain ⟨_, NV₂, aN₂, hmul₂, hdiv₂, hof₂⟩ := hpricing
  -- signs
  have hnav2neg := Number.negative_false_of_pos nav2a hnav2pa
  have hSTneg := Number.negative_false_of_pos v.sharesTotal hSTp
  have hsn₁neg := Number.negative_false_of_pos sn₁ hsnp₁
  have hsn₂pos : 0 < sn₂.toRat := by
    rw [hsnval₂]; exact lt_of_lt_of_le (by rw [← hsnval₁]; exact hsnp₁) hle
  have hsn₂m : sn₂.mantissa_ ≠ 0 :=
    fun h => (ne_of_gt hsn₂pos) (Number.toRat_eq_zero_of_mantissa_zero sn₂ h)
  have hsn₂neg := Number.negative_false_of_pos sn₂ hsn₂pos
  have hsnle : sn₁.toRat ≤ sn₂.toRat := by rw [hsnval₁, hsnval₂]; exact hle
  have hstpos : (0 : ℚ) < ST := lt_of_lt_of_le one_pos hST1
  -- product / quotient exact truths
  set Q : ℚ := nav2a.toRat * sn₁.toRat with hQ_def
  set R : ℚ := nav2a.toRat * sn₂.toRat with hR_def
  have hQpos : 0 < Q := mul_pos hnav2pa hsnp₁
  have hRpos : 0 < R := mul_pos hnav2pa hsn₂pos
  have hQR : Q ≤ R := by rw [hQ_def, hR_def]; exact mul_le_mul_of_nonneg_left hsnle (le_of_lt hnav2pa)
  have hε₂le : (5 : ℚ) / (2 ^ 63 + 7) ≤ 1 := by norm_num
  have hε₂half : (5 : ℚ) / (2 ^ 63 + 7) ≤ 1 / 2 := by norm_num
  have hε₃le : (6 : ℚ) / (2 ^ 63 - 3) ≤ 1 := by norm_num
  -- run 1 rounding bounds
  have hmul1b : |NV₁.toRat - Q| ≤ Q * (5 / (2 ^ 63 + 7)) := by
    have h : |NV₁.toRat - Q| ≤ |Q| * (5 / (2 ^ 63 + 7)) :=
      operator_mul_rounds_to_nearest nav2a sn₁ NV₁ hnav2na hsnn₁ hmul₁ hNVm₁
    rwa [abs_of_pos hQpos] at h
  have hNV1pos : 0 < NV₁.toRat := by
    have := abs_le.mp hmul1b; nlinarith [hQpos, hε₂le, this.1]
  have hdiv_cl : |aN₁.toRat * ST - NV₁.toRat| ≤ NV₁.toRat * (6 / (2 ^ 63 - 3)) := by
    have hb : |aN₁.toRat - NV₁.toRat / ST| ≤ NV₁.toRat / ST * (6 / (2 ^ 63 - 3)) := by
      have h : |aN₁.toRat - NV₁.toRat / v.sharesTotal.toRat|
          ≤ |NV₁.toRat / v.sharesTotal.toRat| * (6 / (2 ^ 63 - 3)) :=
        operator_div_rounds_to_nearest NV₁ v.sharesTotal aN₁ hNVn₁
          v.wf.sharesTotal_norm hdiv₁ hANm₁
      rwa [← hST_def, abs_of_pos (by positivity : (0 : ℚ) < NV₁.toRat / ST)] at h
    have hrw : aN₁.toRat * ST - NV₁.toRat = (aN₁.toRat - NV₁.toRat / ST) * ST := by field_simp
    rw [hrw, abs_mul, abs_of_pos hstpos]
    calc |aN₁.toRat - NV₁.toRat / ST| * ST
        ≤ (NV₁.toRat / ST * (6 / (2 ^ 63 - 3))) * ST :=
          mul_le_mul_of_nonneg_right hb (le_of_lt hstpos)
      _ = NV₁.toRat * (6 / (2 ^ 63 - 3)) := by
            rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hstpos)]
  -- numeric facts about `σ`
  have hσ82 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-82 : ℤ) :=
    sigma_le_min_stamount
  have h82_8 : (10 : ℚ) ^ (-82 : ℤ) * 8 ≤ 10 ^ (-81 : ℤ) := by
    have he : (10 : ℚ) ^ (-81 : ℤ) = 10 ^ (-82 : ℤ) * 10 := by
      rw [show (-81 : ℤ) = -82 + 1 from by ring, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
    have hp : (0 : ℚ) < (10 : ℚ) ^ (-82 : ℤ) := zpow_pos (by norm_num) _
    rw [he]; nlinarith [hp]
  -- chain the run-1 bounds: `10^-81 · ST ≤ 4·Q`
  have h2NV1 : aN₁.toRat * ST ≤ 2 * NV₁.toRat := by
    have := abs_le.mp hdiv_cl; nlinarith [hNV1pos, hε₃le, this.2]
  have h2Q : NV₁.toRat ≤ 2 * Q := by
    have := abs_le.mp hmul1b; nlinarith [hQpos, hε₂le, this.1]
  have hanchor_ST : (10 : ℚ) ^ (-81 : ℤ) * ST ≤ aN₁.toRat * ST :=
    mul_le_mul_of_nonneg_right hanchor (le_of_lt hstpos)
  have h4Q_ST : (10 : ℚ) ^ (-81 : ℤ) * ST ≤ 4 * Q := by
    have h4 : aN₁.toRat * ST ≤ 4 * Q := by linarith [h2NV1, h2Q]
    linarith [hanchor_ST, h4]
  -- run 2 product stays above `σ`, so `NV₂` does not flush to zero
  have hR_ge : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ R := by
    have hQ1 : (10 : ℚ) ^ (-81 : ℤ) ≤ 4 * Q := by
      calc (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (-81 : ℤ) * 1 := (mul_one _).symm
        _ ≤ (10 : ℚ) ^ (-81 : ℤ) * ST := mul_le_mul_of_nonneg_left hST1 (by positivity)
        _ ≤ 4 * Q := h4Q_ST
    nlinarith [hQR, hQ1, hσ82, h82_8]
  have hNVm₂ : NV₂.mantissa_ ≠ 0 := by
    intro h0
    have hRlt := operator_mul_underflow_truth_small nav2a sn₂ NV₂ .to_nearest hnav2na hsnn₂
      hnav2ma hsn₂m hmul₂ h0
    rw [← hR_def, abs_of_pos hRpos] at hRlt
    linarith [hR_ge, hRlt]
  have hNVn₂ : NV₂.isNormalized :=
    operator_mul_result_isNormalized nav2a sn₂ NV₂ .to_nearest hnav2na hsnn₂
      hnav2ma hsn₂m hmul₂ hNVm₂
  have hmul2b : |NV₂.toRat - R| ≤ R * (5 / (2 ^ 63 + 7)) := by
    have h : |NV₂.toRat - R| ≤ |R| * (5 / (2 ^ 63 + 7)) :=
      operator_mul_rounds_to_nearest nav2a sn₂ NV₂ hnav2na hsnn₂ hmul₂ hNVm₂
    rwa [abs_of_pos hRpos] at h
  have hR2NV2 : R ≤ 2 * NV₂.toRat := by
    have := abs_le.mp hmul2b; nlinarith [hRpos, hε₂half, this.1]
  -- run 2 quotient stays above `σ`, so `aN₂` does not flush to zero
  have hσST : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) * ST ≤ NV₂.toRat := by
    -- 8·NV₂ ≥ 4·R ≥ 4·Q ≥ 10^-81·ST ≥ 8·σ·ST
    have h8NV2 : (10 : ℚ) ^ (-81 : ℤ) * ST ≤ 8 * NV₂.toRat := by
      nlinarith [hQR, hR2NV2, h4Q_ST]
    nlinarith [h8NV2, hσ82, h82_8, hstpos]
  have hNV2pos : 0 < NV₂.toRat := by linarith [hR2NV2, hRpos]
  have haNm₂ : aN₂.mantissa_ ≠ 0 := by
    intro h0
    have hlt := operator_div_underflow_truth_small NV₂ v.sharesTotal aN₂ .to_nearest hNVn₂
      v.wf.sharesTotal_norm hNVm₂ hSTm hdiv₂ h0
    rw [← hST_def, abs_of_pos (div_pos hNV2pos hstpos)] at hlt
    rw [div_lt_iff₀ hstpos] at hlt
    linarith [hσST, hlt]
  have hANn₂ : aN₂.isNormalized :=
    operator_div_result_isNormalized NV₂ v.sharesTotal aN₂ .to_nearest hNVn₂
      v.wf.sharesTotal_norm hNVm₂ hSTm hdiv₂ haNm₂
  -- pricing chain monotone, then downward floor monotone
  have haNle : aN₁.toRat ≤ aN₂.toRat :=
    Number.mul_div_num_mono nav2a v.sharesTotal sn₁ sn₂ NV₁ NV₂ aN₁ aN₂
      hnav2na hnav2ma hnav2neg v.wf.sharesTotal_norm hSTm hSTneg
      hsnn₁ hsnm₁ hsn₁neg hsnn₂ hsn₂m hsn₂neg
      hmul₁ hNVm₁ hmul₂ hNVm₂ hdiv₁ hANm₁ hdiv₂ haNm₂ hsnle
  exact ofNumber_downward_toRat_mono v.numericType aN₁ aN₂ assets₁ assets₂
    hANn₁ haN₁neg hANm₁ hANn₂ (Number.negative_false_of_pos aN₂ (by
      exact lt_of_lt_of_le hANp₁ haNle)) haNm₂ hof₁ hof₂ haNle

/-- `computeWithdrawBy{Shares,Assets}` prices the redeemed shares: the payout equals
`sharesToAssetsWithdraw cw.sharesRedeemed`. -/
lemma computeWithdraw_price_eq (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (cw : ComputeWithdrawResult)
    (hcomp : (match amount with
      | .vaultAssets a => computeWithdrawByAssets v a waive
      | .vaultShares s => computeWithdrawByShares v s waive) = .ok cw)
    (herr : cw.error = none) :
    v.sharesToAssetsWithdraw cw.sharesRedeemed waive = .ok cw.assets' := by
  cases amount with
  | vaultShares s =>
    simp only [] at hcomp
    obtain ⟨hprice, hsr⟩ := computeWithdrawByShares_none_reduces v s waive cw hcomp herr
    rw [hsr]; exact hprice
  | vaultAssets a =>
    simp only [] at hcomp
    obtain ⟨sh, _, _, hprice, hsr⟩ := computeWithdrawByAssets_none_reduces v a waive cw hcomp herr
    rw [hsr]; exact hprice

/-- **Raw priced payout is monotone in shares burned.** A successful non-final
withdrawal first computes this raw amount with `sharesToAssetsWithdraw`; only then
it clamps the negated amount to obtain the returned final debit.  The theorem
therefore deliberately returns the two raw amounts instead of identifying either
with `r.assets'`.  Transporting this order through the dynamic post-sum clamp
requires the explicit source-path classifier/grid evidence supplied by
`WithdrawPostSumMono` and `WithdrawClampMono`; it is not an equality rewrite. -/
theorem Vault.withdraw_raw_payout_monotone_proof (v : Vault) (amount₁ amount₂ : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount)
    (r₁ r₂ : WithdrawResult)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hcb₁ : r₁.sharesBurned.Canonical) (hcb₂ : r₂.sharesBurned.Canonical)
    (hnnb₁ : 0 ≤ r₁.sharesBurned.toRat) (hnnb₂ : 0 ≤ r₂.sharesBurned.toRat)
    (hok₁ : v.withdraw amount₁ waiveUnrealizedLoss = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : v.withdraw amount₂ waiveUnrealizedLoss = .ok r₂) (herr₂ : r₂.error = none)
    (_hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (_hfin₁ : r₁.sharesBurned.operator_eq sharesTotalAmount = false)
    (_hfin₂ : r₂.sharesBurned.operator_eq sharesTotalAmount = false)
    (hle : r₁.sharesBurned.toRat ≤ r₂.sharesBurned.toRat) :
    ∃ raw₁ raw₂ : STAmount,
      v.sharesToAssetsWithdraw r₁.sharesBurned waiveUnrealizedLoss = .ok raw₁ ∧
      v.sharesToAssetsWithdraw r₂.sharesBurned waiveUnrealizedLoss = .ok raw₂ ∧
      raw₁.toRat ≤ raw₂.toRat := by
  have hprice : ∀ (amount : WithdrawAmount) (r : WithdrawResult),
      v.withdraw amount waiveUnrealizedLoss = .ok r → r.error = none →
      ∃ raw : STAmount,
        v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok raw := by
    intro amount r hok herr
    obtain ⟨cw, _, _, hcomp, hcwerr, _, _, _, hsbeq, _⟩ :=
      Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr
    refine ⟨cw.assets', ?_⟩
    rw [hsbeq]
    exact computeWithdraw_price_eq v amount waiveUnrealizedLoss cw hcomp hcwerr
  obtain ⟨raw₁, hp₁⟩ := hprice amount₁ r₁ hok₁ herr₁
  obtain ⟨raw₂, hp₂⟩ := hprice amount₂ r₂ hok₂ herr₂
  exact ⟨raw₁, raw₂, hp₁, hp₂,
    sharesToAssetsWithdraw_mono v waiveUnrealizedLoss
      r₁.sharesBurned r₂.sharesBurned raw₁ raw₂
      hcb₁ hnnb₁ hcb₂ hnnb₂ hnav hp₁ hp₂ hle⟩

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Evidence that transports raw withdrawal-payout order through the actual
post-sum clamp.  It deliberately separates the executable cases: integral
clamps sign-clear; a zero lower final debit is ordered by final nonnegativity;
and nonzero fractional payouts require the post-sum scales selected by the two
successful clamp executions.  The latter scale relation is the precise output
of the ordinary/cusp classifier layer, not a raw/final equality. -/
inductive Vault.WithdrawFinalDebitOrderEvidence (v : Vault)
    (raw₁ raw₂ final₁ final₂ : STAmount) : Prop where
  | integral
      (h₁ : raw₁.integral = true) (h₂ : raw₂.integral = true) :
      Vault.WithdrawFinalDebitOrderEvidence v raw₁ raw₂ final₁ final₂
  | zeroLower
      (hfinal₁ : final₁.toRat = 0) (hfinal₂ : 0 ≤ final₂.toRat) :
      Vault.WithdrawFinalDebitOrderEvidence v raw₁ raw₂ final₁ final₂
  | fractional
      (hc₁ : raw₁.IOUCanonical) (hc₂ : raw₂.IOUCanonical)
      (s₁ s₂ : Int)
      (hs₁lo : (-96 : Int) ≤ s₁) (hs₁hi : s₁ ≤ 80)
      (hs₂hi : s₂ ≤ 80) (hs₂domain : s₂ = -100 ∨ (-81 : Int) ≤ s₂)
      (hscale : s₂ ≤ s₁)
      (hpost₁ : postSumExponent v.assetsTotal raw₁.operator_neg = .ok s₁)
      (hpost₂ : postSumExponent v.assetsTotal raw₂.operator_neg = .ok s₂)
      (hneg₁ : raw₁.operator_neg.negative = true)
      (hneg₂ : raw₂.operator_neg.negative = true) :
      Vault.WithdrawFinalDebitOrderEvidence v raw₁ raw₂ final₁ final₂

/-- **Classified final-debit monotonicity.** This is the source-faithful
replacement for the stale raw-equals-final proof: two successful non-final
withdrawals supply their raw pricing results and their actual clamp results;
then an integral, zero, or fractional post-sum-grid certificate transports the
raw order to the returned final debits.  In the fractional case the certificate
must come from the concrete normal-cell/exceptional-cusp classification of the
two post-sum additions. -/
theorem Vault.withdraw_final_debit_monotone_classified_proof
    (v : Vault) (waiveUnrealizedLoss : Bool)
    (shares₁ shares₂ raw₁ raw₂ final₁ final₂ : STAmount)
    (hshares₁ : shares₁.Canonical) (hshares₂ : shares₂.Canonical)
    (hnn₁ : 0 ≤ shares₁.toRat) (hnn₂ : 0 ≤ shares₂.toRat)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hprice₁ : v.sharesToAssetsWithdraw shares₁ waiveUnrealizedLoss = .ok raw₁)
    (hprice₂ : v.sharesToAssetsWithdraw shares₂ waiveUnrealizedLoss = .ok raw₂)
    (hshares : shares₁.toRat ≤ shares₂.toRat)
    (hclamp₁ : clampToSumExponent v.assetsTotal raw₁.operator_neg = .ok final₁)
    (hclamp₂ : clampToSumExponent v.assetsTotal raw₂.operator_neg = .ok final₂)
    (hclassified : Vault.WithdrawFinalDebitOrderEvidence v raw₁ raw₂ final₁ final₂) :
    final₁.toRat ≤ final₂.toRat := by
  have hraw : raw₁.toRat ≤ raw₂.toRat :=
    sharesToAssetsWithdraw_mono v waiveUnrealizedLoss shares₁ shares₂ raw₁ raw₂
      hshares₁ hnn₁ hshares₂ hnn₂ hnav hprice₁ hprice₂ hshares
  have hraw₁_nonneg : 0 ≤ raw₁.toRat :=
    (Vault.sharesToAssetsWithdraw_spec v shares₁ raw₁ waiveUnrealizedLoss
      hnn₁ hshares₁ hnav hprice₁).1
  have hraw₂_nonneg : 0 ≤ raw₂.toRat :=
    (Vault.sharesToAssetsWithdraw_spec v shares₂ raw₂ waiveUnrealizedLoss
      hnn₂ hshares₂ hnav hprice₂).1
  cases hclassified with
  | integral hint₁ hint₂ =>
      exact Vault.clampToSumExponent_withdraw_integral_mono v raw₁ raw₂ final₁ final₂
        hint₁ hint₂ hraw hraw₁_nonneg hraw₂_nonneg hclamp₁ hclamp₂
  | zeroLower hfinal₁ hfinal₂ =>
      rw [hfinal₁]
      exact hfinal₂
  | fractional hc₁ hc₂ s₁ s₂ hs₁lo hs₁hi hs₂hi hs₂domain hscale hpost₁ hpost₂ hneg₁ hneg₂ =>
      exact Vault.clampToSumExponent_withdraw_fractional_mono
        v raw₁ raw₂ final₁ final₂ s₁ s₂ hc₁ hc₂ hs₁lo hs₁hi hs₂hi hs₂domain
        hraw₁_nonneg hraw hscale hpost₁ hpost₂ hneg₁ hneg₂ hclamp₁ hclamp₂


end XRPL.Model.SingleAssetVault
