import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128Facts
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128.RoundDiv

namespace XRPL.Model.Protocol

/-! # `doNormalize128` round-decision facts (tight, for the div cusp-monotone route)

Augments `doNormalize128_algorithmic_facts` with the *tight* round-decision facts
(`g.round ⋛ 1 ↔ f ⋛ 1/2` for the true value fraction `f`, not the coarse shadow),
by threading the `RoundDiv` value invariant through the same `scaleUp / scaleDown /
capAtMaxRep` walk and discharging the `p = 0` corner via `valueInv_p0_le_half`. -/

set_option maxHeartbeats 25600000 in
-- Full `doNormalize128` walk (scaleUp/scaleDown/capAtMaxRep/doRoundUp) threading two
-- invariants (shadow repr + value repr); mirrors `doNormalize128_algorithmic_facts`.
theorem doNormalize128_algorithmic_facts_round
    (zn : Bool) (M : UInt128) (e : Int) (δ : ℚ) (sticky : Bool) (mode : rounding_mode)
    (hδ_low : 0 ≤ δ) (hδ_lt : δ < 1)
    (hsticky_zero : sticky = false → δ = 0)
    (hsticky_pos : sticky = true → 0 < δ)
    (hM_pos : 1 ≤ M.toNat) (hM_lt : M.toNat < 10 ^ 23)
    (hδM : sticky = true → δ * 10 ^ 20 ≤ (M.toNat : ℚ))
    (result : Number)
    (hok : doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result)
    (hres : result.mantissa_ ≠ 0) :
    ∃ (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult),
      mantissaFloor ≤ zm.toNat ∧
      zm.toNat ≤ maxRepUp.toNat ∧
      0 ≤ f ∧ f < 1 ∧
      (zm.toNat = mantissaFloor → (8 : ℚ) / 10 ≤ f) ∧
      ((M.toNat : ℚ) + δ) * 10 ^ e = ((zm.toNat : ℚ) + f) * 10 ^ ze' ∧
      g.doRoundUp false zm ze' largeRange.min largeRange.max mode
        .normalize2 = .ok res_pos ∧
      |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ ∧
      res_pos.mantissa_ ≠ 0 ∧
      result.negative_ = zn ∧
      mantissaFloorSucc ≤ zm.toNat ∧
      (g.round .to_nearest = 1 → f > 1 / 2) ∧
      (g.round .to_nearest = 0 → f = 1 / 2) ∧
      (f > 1 / 2 → g.round .to_nearest = 1) ∧
      (f = 1 / 2 → g.round .to_nearest = 0) := by
  have hminM_v : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
  have hmaxM_v : largeRange.max.toNat = 9999999999999999999 := largeRange_max_val
  have hM_ne : ¬ (M == 0) = true := by
    intro h
    have : M = 0 := by exact_mod_cast beq_iff_eq.mp h
    rw [this] at hM_pos; simp at hM_pos
  unfold doNormalize128 at hok
  rw [if_neg hM_ne] at hok
  simp only [] at hok
  rcases hsu : doNormalize128.scaleUp largeRange.min M e with ⟨M₁, e₁⟩
  rw [hsu] at hok
  simp only [] at hok
  obtain ⟨hval_su, hM₁_pos, hM₁_lt, he₁_le, hM₁_size⟩ :
      ((M₁.toNat : ℚ) * 10 ^ e₁ = (M.toNat : ℚ) * 10 ^ e)
      ∧ 1 ≤ M₁.toNat ∧ M₁.toNat < 10 ^ 23 ∧ e₁ ≤ e
      ∧ (M₁ = M ∧ e₁ = e ∨ M₁.toNat < 10 ^ 19) := by
    have hfacts := doNormalize128_scaleUp_facts largeRange.min M e hminM_v hM_pos hM_lt
    rw [hsu] at hfacts; exact hfacts
  have h10e_pos : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  have h10e₁_pos : (0 : ℚ) < (10 : ℚ) ^ e₁ := zpow_pos (by norm_num) _
  set δ₁ : ℚ := δ * 10 ^ (e - e₁) with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := mul_nonneg hδ_low (le_of_lt (zpow_pos (by norm_num) _))
  have hδ₁_zero : sticky = false → δ₁ = 0 := by
    intro hst; rw [hδ₁_def, hsticky_zero hst, zero_mul]
  have hδ₁_pos : sticky = true → 0 < δ₁ := fun hst =>
    mul_pos (hsticky_pos hst) (zpow_pos (by norm_num) _)
  have hval₁ : ((M₁.toNat : ℚ) + δ₁) * 10 ^ e₁ = ((M.toNat : ℚ) + δ) * 10 ^ e := by
    rw [hδ₁_def, add_mul, add_mul, hval_su]
    congr 1
    rw [show δ * 10 ^ (e - e₁) * 10 ^ e₁ = δ * (10 ^ (e - e₁) * 10 ^ e₁) from by ring,
        ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), show e - e₁ + e₁ = e from by omega]
  have hδ₁M : δ₁ * 10 ^ 20 ≤ (M₁.toNat : ℚ) := by
    by_cases hst : sticky = true
    · have h := hδM hst
      have lhs_eq : δ₁ * 10 ^ 20 * 10 ^ e₁ = δ * 10 ^ 20 * 10 ^ e := by
        rw [hδ₁_def,
            show δ * 10 ^ (e - e₁) * 10 ^ 20 * 10 ^ e₁
              = δ * 10 ^ 20 * (10 ^ (e - e₁) * 10 ^ e₁) from by ring,
            ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), show e - e₁ + e₁ = e from by omega]
      have hfin : δ₁ * 10 ^ 20 * 10 ^ e₁ ≤ (M₁.toNat : ℚ) * 10 ^ e₁ := by
        rw [lhs_eq, hval_su]
        exact mul_le_mul_of_nonneg_right h (le_of_lt h10e_pos)
      exact le_of_mul_le_mul_right hfin h10e₁_pos
    · rw [Bool.not_eq_true] at hst
      rw [hδ₁_zero hst, zero_mul]; exact Nat.cast_nonneg _
  have hδ₁_lt : δ₁ < 1 := by
    rcases hM₁_size with ⟨_, heeq⟩ | hlt19
    · rw [hδ₁_def, heeq, sub_self, zpow_zero, mul_one]; exact hδ_lt
    · have hM₁q : (M₁.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hlt19
      nlinarith [hδ₁M, hM₁q, hδ₁_nn]
  set g₀ : Guard := (if sticky = true
      then (if zn then Guard.new.set_negative else Guard.new).set_sticky
      else (if zn then Guard.new.set_negative else Guard.new)) with hg₀_def
  set ftilde₀ : ℚ := (if sticky = true then (1 : ℚ) / 10 ^ 17 else 0) with hft₀_def
  have hrep₀ : represents g₀ ftilde₀ := by
    rw [hg₀_def, hft₀_def]
    by_cases hst : sticky = true
    · rw [if_pos hst, if_pos hst]; exact represents_sticky_initial128 zn
    · rw [if_neg hst, if_neg hst]; exact represents_initial128 zn
  have h_g0_sbit : g₀.sbit_ = zn := by
    rw [hg₀_def]
    by_cases hst : sticky = true
    · rw [if_pos hst]
      by_cases hz : zn
      · rw [if_pos hz, hz]; rfl
      · rw [if_neg hz]; rw [Bool.not_eq_true] at hz; rw [hz]; rfl
    · rw [if_neg hst]
      by_cases hz : zn
      · rw [if_pos hz, hz]; rfl
      · rw [if_neg hz]; rw [Bool.not_eq_true] at hz; rw [hz]; rfl
  -- === value-invariant setup for g₀ ===
  have hg0_digits : g₀.digits_ = 0 := by
    rw [hg₀_def]; by_cases hst : sticky = true
    · rw [if_pos hst]; cases zn <;> rfl
    · rw [if_neg hst]; cases zn <;> rfl
  have hg0_dv : decimalValue g₀.digits_ = 0 := by rw [hg0_digits, decimalValue_zero]
  have hg0_all : allNibblesAtMost9 g₀.digits_ := by rw [hg0_digits]; exact allNibblesAtMost9_zero
  have hg0_xbit : g₀.xbit_ = sticky := by
    rw [hg₀_def]; by_cases hst : sticky = true
    · rw [if_pos hst, hst]; cases zn <;> rfl
    · rw [if_neg hst]; rw [Bool.not_eq_true] at hst; rw [hst]; cases zn <;> rfl
  have hg0_xbit_iff : g₀.xbit_ = true ↔ 0 < δ₁ := by
    rw [hg0_xbit]; constructor
    · intro h; exact hδ₁_pos h
    · intro h; by_contra hns; rw [Bool.not_eq_true] at hns
      rw [hδ₁_zero hns] at h; exact lt_irrefl 0 h
  have hvval0 : δ₁ = (decimalValue g₀.digits_ : ℚ) / 10 ^ 16 + δ₁ := by
    rw [hg0_dv, Nat.cast_zero, zero_div, zero_add]
  have hvxlt0 : δ₁ < 1 / 10 ^ 0 := by simpa using hδ₁_lt
  have hvdvd0 : (10 : ℕ) ^ 16 ∣ decimalValue g₀.digits_ * 10 ^ 0 := by
    rw [hg0_dv, Nat.zero_mul]; exact dvd_zero _
  have hvsize0 : M₁.toNat * 10 ^ 0 < 10 ^ 23 := by rw [pow_zero, Nat.mul_one]; exact hM₁_lt
  have hvcouple0 : δ₁ * 10 ^ 20 ≤ (M₁.toNat : ℚ) * 10 ^ 0 := by rw [pow_zero, mul_one]; exact hδ₁M
  cases hsd : doNormalize_scaleDown128 largeRange.max M₁ e₁ g₀ with
  | error err => except_clash hsd hok
  | ok sd =>
    rw [hsd] at hok
    simp only [] at hok
    obtain ⟨φ₂, ftilde₂, h2nn, h2lt, h2rep, h2slip, h2val, h2le, h2lt22, h2exp, h2sbit, h2xbit,
            h2pos, h2lt1⟩ :=
      doNormalize_scaleDown128_repr largeRange.max M₁ e₁ g₀ hmaxM_v δ₁ ftilde₀
        hδ₁_nn (le_of_lt hδ₁_lt) hrep₀ hM₁_lt sd hsd
    -- value-invariant through scaleDown
    obtain ⟨φ₂v, x₂, p₂, hv2nn, hv2lt, hv2val, hv2xbit, hv2all, hv2dvd, hv2size, hv2couple, hv2veq⟩ :=
      doNormalize_scaleDown128_valueInv largeRange.max M₁ e₁ g₀ hmaxM_v δ₁ δ₁ 0
        hδ₁_nn hvxlt0 hvval0 hg0_xbit_iff hg0_all hvdvd0 hvsize0 hvcouple0 sd hsd
    by_cases hund : (sd.2.1 < minExponent || sd.1 < toUInt128 largeRange.min) = true
    · rw [if_pos hund] at hok
      exfalso; apply hres
      have h := Except.ok.inj hok; rw [← h]; rfl
    · rw [if_neg hund] at hok
      rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hund
      obtain ⟨hund1, hund2⟩ := hund
      have hM₂_ge : 1000000000000000000 ≤ sd.1.toNat := by
        by_contra h; push_neg at h
        apply absurd (decide_eq_true (show sd.1 < toUInt128 largeRange.min from by
          rw [BitVec.lt_def, toNat_toUInt128, hminM_v]; exact h))
        rw [hund2]; simp
      have hM₂_fit : sd.1.toNat < 2 ^ 64 := by rw [hmaxM_v] at h2le; omega
      have hM₂u_toNat : (toUInt64 sd.1).toNat = sd.1.toNat := toNat_toUInt64 hM₂_fit
      cases hcap : doNormalize_capAtMaxRep (toUInt64 sd.1) sd.2.1 sd.2.2 with
      | error err => except_clash hcap hok
      | ok cp =>
        rw [hcap] at hok
        simp only [] at hok
        obtain ⟨φ₃, ftilde₃, h3nn, h3lt, h3rep, h3slip, h3val, h3floor, h3le, h3exp, h3sbit, h3xbit,
                h3pos, h3lt1⟩ :=
          doNormalize_capAtMaxRep_repr (toUInt64 sd.1) sd.2.1 sd.2.2
            (by rw [hM₂u_toNat]; exact hM₂_ge)
            (by rw [hM₂u_toNat]; rw [hmaxM_v] at h2le; exact h2le)
            φ₂ ftilde₂ h2nn h2lt h2rep cp hcap
        -- value-invariant through capAtMaxRep
        obtain ⟨φ₃v, x₃, p₃, hv3nn, hv3lt, hv3val, hv3xbit, hv3all, hv3dvd, hv3size, hv3couple, hv3veq⟩ :=
          doNormalize_capAtMaxRep_valueInv (toUInt64 sd.1) sd.2.1 sd.2.2
            φ₂v x₂ p₂ hv2nn hv2lt hv2val hv2xbit hv2all hv2dvd
            (by rw [hM₂u_toNat]; exact hv2size)
            (by rw [hM₂u_toNat]; exact hv2couple)
            cp hcap
        cases hru : cp.2.2.doRoundUp zn cp.1 cp.2.1 largeRange.min largeRange.max
            mode .normalize2 with
        | error err => except_clash hru hok
        | ok res =>
          rw [hru] at hok
          have h_result : result = res.toNumber := (Except.ok.inj hok).symm
          have hres_mant : res.mantissa_ ≠ 0 := by rw [h_result] at hres; exact hres
          set res_pos : RoundResult :=
            { negative_ := false, mantissa_ := res.mantissa_, exponent_ := res.exponent_ }
            with hres_pos_def
          have h_rup_pos : cp.2.2.doRoundUp false cp.1 cp.2.1 largeRange.min largeRange.max
              mode .normalize2 = .ok res_pos :=
            doRoundUp_false_from_ok cp.2.2 zn cp.1 cp.2.1 mode .normalize2 res hru
          have hres_pos_mant : res_pos.mantissa_ ≠ 0 := hres_mant
          have h_value : ((cp.1.toNat : ℚ) + φ₃) * 10 ^ cp.2.1
              = ((M.toNat : ℚ) + δ) * 10 ^ e := by
            rw [← h3val, hM₂u_toNat, ← h2val, hval₁]
          have h_abs : |result.toRat|
              = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := by
            rw [h_result, abs_toRat_eq res.toNumber]; rfl
          have h_neg : result.negative_ = zn := by
            rw [h_result]
            exact doRoundUp_negative_of_mant_ne cp.2.2 zn cp.1 cp.2.1 _ _ _
              .normalize2 res hru hres_mant
          -- reconcile the value fractions: φ₃v = φ₃
          have h_value_v : ((cp.1.toNat : ℚ) + φ₃v) * 10 ^ cp.2.1
              = ((M.toNat : ℚ) + δ) * 10 ^ e := by
            rw [← hv3veq, hM₂u_toNat, ← hv2veq, hval₁]
          have h10cp : (0 : ℚ) < (10 : ℚ) ^ cp.2.1 := zpow_pos (by norm_num) _
          have hφeq : φ₃v = φ₃ := by
            have := h_value_v.trans h_value.symm
            have h2 : (cp.1.toNat : ℚ) + φ₃v = (cp.1.toNat : ℚ) + φ₃ :=
              mul_right_cancel₀ (ne_of_gt h10cp) this
            linarith [h2]
          -- the value invariant, at the true fraction f = φ₃
          have hv3val' : φ₃ = (decimalValue cp.2.2.digits_ : ℚ) / 10 ^ 16 + x₃ := by
            rw [← hφeq]; exact hv3val
          have hzm_le_ru : cp.1.toNat ≤ maxRepUp.toNat := by
            rw [show maxRepUp.toNat = maxRepUpNat from rfl]; exact h3le
          have hzm_lt19 : cp.1.toNat < 10 ^ 19 := by
            rw [show maxRepUp.toNat = maxRepUpNat from rfl] at hzm_le_ru
            have : (maxRepUpNat : ℕ) < 10 ^ 19 := by norm_num
            omega
          -- p₃ = 0 corner discharge
          have hp0 : p₃ = 0 → φ₃ < 1 / 2 := by
            intro hp0eq
            subst hp0eq
            exact valueInv_p0_le_half cp.2.2 φ₃ x₃ cp.1.toNat hv3val' hv3all hv3dvd hv3couple hzm_lt19
          -- round-decision facts
          have hround1 : cp.2.2.round .to_nearest = 1 → φ₃ > 1 / 2 := fun h1 =>
            div_round_eq_one cp.2.2 φ₃ x₃ hv3nn hv3val' hv3xbit hv3all h1
          have hround0 : cp.2.2.round .to_nearest = 0 → φ₃ = 1 / 2 := fun h0 =>
            div_round_eq_zero cp.2.2 φ₃ x₃ hv3nn hv3val' hv3xbit hv3all h0
          have hfgt : φ₃ > 1 / 2 → cp.2.2.round .to_nearest = 1 := fun h =>
            div_f_gt_half cp.2.2 φ₃ x₃ p₃ hv3nn hv3lt hv3val' hv3xbit hv3all hv3dvd hp0 h
          have hfeq : φ₃ = 1 / 2 → cp.2.2.round .to_nearest = 0 := fun h =>
            div_f_eq_half cp.2.2 φ₃ x₃ p₃ hv3nn hv3lt hv3val' hv3xbit hv3all hv3dvd hp0 h
          exact ⟨cp.1, cp.2.1, φ₃, cp.2.2, res_pos,
            le_of_lt h3floor, hzm_le_ru, h3nn, h3lt1 (h2lt1 hδ₁_lt),
            (fun heq => absurd heq (by omega)),
            h_value.symm, h_rup_pos, h_abs, hres_pos_mant, h_neg, by omega,
            hround1, hround0, hfgt, hfeq⟩

end XRPL.Model.Protocol
