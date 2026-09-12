import XRPL.Properties.Vault.Common.RoundMonotoneCusp
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard

/-! # `RoundsCuspAware` satisfaction for `operator_mul` / `operator_div`

Establishes `op x y … = .ok r → r.RoundsCuspAware (truth)`, the linchpin that makes
`operator_*_mono_of_cuspAware` unconditional. Uses the algorithmic decomposition
`truth = (zm + f)·10^ze'`, `branchA`/`branchB` to pin the neighbour `r` equals, and
`no_normalized_in_open_ulp_gap_pos_zm` to bound the *other* neighbour to the cell
top/bottom (needing no explicit grid-point construction). -/

namespace XRPL.Model.Protocol

/-- The upper neighbour of `t` clears the cell top `(k+1)·10^e` when `k·10^e < t`
and `k` is a valid scaled mantissa. -/
theorem upper_ge_cell_top (t : ℚ) (U : Number) (hU : Number.upper t = some U)
    (k : ℕ) (e : ℤ) (hk_ge : mantissaFloorSucc ≤ k) (hk_lt : k < 10 ^ 19)
    (ht_lo : (k : ℚ) * 10 ^ e < t) :
    ((k : ℚ) + 1) * 10 ^ e ≤ U.toRat := by
  have hUge : t ≤ U.toRat := Number.upper_ge t U hU
  have hUpos : 0 < U.toRat := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ht_lo) hUge
  by_contra h
  push_neg at h
  exact no_normalized_in_open_ulp_gap_pos_zm e k hk_ge hk_lt U
    (Number.upper_isNormalized t U hU) hUpos (lt_of_lt_of_le ht_lo hUge) h

/-- The lower neighbour of `t` stays at/below the cell bottom `k·10^e` when
`t < (k+1)·10^e` and `k` is a valid scaled mantissa. -/
theorem lower_le_cell_bot (t : ℚ) (L : Number) (hL : Number.lower t = some L)
    (k : ℕ) (e : ℤ) (hk_ge : mantissaFloorSucc ≤ k) (hk_lt : k < 10 ^ 19)
    (ht_hi : t < ((k : ℚ) + 1) * 10 ^ e) :
    L.toRat ≤ (k : ℚ) * 10 ^ e := by
  have hLle : L.toRat ≤ t := Number.lower_le t L hL
  by_contra h
  push_neg at h  -- k·10^e < L.toRat
  have hLpos : 0 < L.toRat := lt_of_le_of_lt (by positivity) h
  exact no_normalized_in_open_ulp_gap_pos_zm e k hk_ge hk_lt L
    (Number.lower_isNormalized t L hL) hLpos h (lt_of_le_of_lt hLle ht_hi)

/-- Cusp analog: the upper neighbour clears `maxRepUp·10^e` when `maxRep·10^e < t`
(no representable sits in the width-3 cusp gap). -/
theorem upper_ge_cusp_top (t : ℚ) (U : Number) (hU : Number.upper t = some U) (e : ℤ)
    (ht_lo : (maxRepNat : ℚ) * 10 ^ e < t) :
    (maxRepUpNat : ℚ) * 10 ^ e ≤ U.toRat := by
  have hUge : t ≤ U.toRat := Number.upper_ge t U hU
  have hmaxR : (maxRep.toNat : ℚ) = (maxRepNat : ℚ) := by rw [maxRep_val]; norm_num
  have hUpos : 0 < U.toRat :=
    lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ht_lo) hUge
  by_contra h
  push_neg at h
  exact no_normalized_in_cusp_gap_pos e U (Number.upper_isNormalized t U hU) hUpos
    (by rw [hmaxR]; exact lt_of_lt_of_le ht_lo hUge)
    (by rw [show (maxRepCuspTarget : ℚ) = (maxRepUpNat : ℚ) from by norm_num]; exact h)

/-- Cusp analog: the lower neighbour stays at/below `maxRep·10^e` when
`t < maxRepUp·10^e`. -/
theorem lower_le_cusp_bot (t : ℚ) (L : Number) (hL : Number.lower t = some L) (e : ℤ)
    (ht_hi : t < (maxRepUpNat : ℚ) * 10 ^ e) :
    L.toRat ≤ (maxRepNat : ℚ) * 10 ^ e := by
  have hLle : L.toRat ≤ t := Number.lower_le t L hL
  have hmaxR : (maxRep.toNat : ℚ) = (maxRepNat : ℚ) := by rw [maxRep_val]; norm_num
  by_contra h
  push_neg at h
  have hLpos : 0 < L.toRat := lt_of_le_of_lt (by positivity) h
  exact no_normalized_in_cusp_gap_pos e L (Number.lower_isNormalized t L hL) hLpos
    (by rw [hmaxR]; exact h)
    (by rw [show (maxRepCuspTarget : ℚ) = (maxRepUpNat : ℚ) from by norm_num]
        exact lt_of_le_of_lt hLle ht_hi)

/-- Coarse analog: above `maxRepUp` the grid step is `10·10^e`, so the upper
neighbour clears `(maxRepUp+10)·10^e` when `maxRepUp·10^e < t`. -/
theorem upper_ge_coarse_top (t : ℚ) (U : Number) (hU : Number.upper t = some U) (e : ℤ)
    (ht_lo : (maxRepUpNat : ℚ) * 10 ^ e < t) :
    (twoPow63Add12 : ℚ) * 10 ^ e ≤ U.toRat := by
  have hUge : t ≤ U.toRat := Number.upper_ge t U hU
  have hUpos : 0 < U.toRat := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ht_lo) hUge
  by_contra h
  push_neg at h
  exact no_normalized_in_upper_cusp_gap_pos e U (Number.upper_isNormalized t U hU) hUpos
    (by rw [show (maxRepCuspTarget : ℚ) = (maxRepUpNat : ℚ) from by norm_num]
        exact lt_of_lt_of_le ht_lo hUge) h

/-! ## Cusp-interior pushOverflow decision -/

/-- Pushing decimal digit `6` makes the guard round up (top nibble `6 > 5`). -/
lemma push6_round_one (g : Guard) : (g.push 6).round .to_nearest = 1 := by
  have h260 : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have hd : (g.push 6).digits_.toNat = g.digits_.toNat / 16 + 6 * 2 ^ 60 := by
    rw [toNat_push_digits, show (6 : UInt64).toNat % 16 = 6 from by decide]
  have hthr : (0x5000_0000_0000_0000 : UInt64).toNat = 5 * 2 ^ 60 := by decide
  have hgt : (0x5000_0000_0000_0000 : UInt64) < (g.push 6).digits_ := by
    rw [UInt64.lt_iff_toNat_lt, hthr, hd, h260]; omega
  have hne : ¬ (g.push 6).empty := by
    unfold Guard.empty Guard.unrecoverable
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true, not_and]
    intro hz
    have hz0 : (g.push 6).digits_.toNat = 0 := by rw [hz]; rfl
    rw [hd, h260] at hz0; omega
  rw [round_to_nearest_def hne, if_pos hgt]

/-- **Cusp-interior down forces `zm = maxRep+1` and `f < ½`.** In the strict cusp
`maxRep < zm < maxRepUp` (so `zm ∈ {maxRep+1, maxRep+2}`), if `doRoundUp`'s
pushOverflow-adjusted round decision is `false` (rounds down to `maxRep`), then
`zm = maxRep+1` and the fractional position is below `½`. At `zm = maxRep+2` the
overflow digit `6` always rounds up, so `zm = maxRep+2` is excluded; at
`zm = maxRep+1` the down decision means the midpoint bump did not fire, i.e.
`g.round ∉ {0,1}`, i.e. `f < ½`. -/
theorem cusp_interior_down_forces (g : Guard) (zm : UInt64) (f : ℚ) (hf : represents g f)
    (hlo : maxRep.toNat < zm.toNat) (hhi : zm.toNat < maxRepUp.toNat)
    (hdec : ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
       || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = false) :
    zm.toNat = maxRep.toNat + 1 ∧ f < 1 / 2 := by
  have hmaxR : maxRep.toNat = maxRepNat := maxRep_val
  have hmaxRU : maxRepUp.toNat = maxRepUpNat := rfl
  have hcase : zm.toNat = maxRepNat + 1 ∨ zm.toNat = maxRepNat + 2 := by omega
  rcases hcase with hz1 | hz2
  · -- zm = maxRep + 1
    have hzeq : zm = 9223372036854775808 := UInt64.toNat_inj.mp (by rw [hz1]; decide)
    -- the pushOverflow reduces (per the midpoint bump) to `push 6` (bump) or `push 3` (no bump)
    have hpo_bump : (g.round .to_nearest == 1 || g.round .to_nearest == 0) = true →
        g.pushOverflow zm .to_nearest = g.push 6 := by
      intro hr
      rw [hzeq]; unfold Guard.pushOverflow
      rw [if_pos (by decide : maxRep ≤ (9223372036854775808 : UInt64) ∧
        (9223372036854775808 : UInt64) < maxRepUp)]
      simp only [show ((9223372036854775808 : UInt64) % 10 < 9) = true from by decide, if_true,
        show (maxRep + (maxRepUp - maxRep) / 2) = (9223372036854775808 : UInt64) from by decide,
        show ((9223372036854775808 : UInt64) == 9223372036854775808) = true from by decide,
        Bool.and_true, if_pos hr,
        show ((9223372036854775808 : UInt64) + 1 == maxRep) = false from by decide,
        Bool.false_eq_true, if_false,
        show ((9223372036854775808 : UInt64) + 1 - maxRep) * 10 / (maxRepUp - maxRep) = 6 from by decide]
    -- decision false forces the ¬bump branch; bump would push 6 → decision true
    have hnobump : ¬ ((g.round .to_nearest == 1 || g.round .to_nearest == 0) = true) := by
      intro hr
      rw [hpo_bump hr, push6_round_one] at hdec
      simp only [beq_self_eq_true, Bool.true_or] at hdec
      exact absurd hdec (by decide)
    -- g.round ∉ {0,1}
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnobump
    obtain ⟨hr1, hr0⟩ := hnobump
    have hflt : f < 1 / 2 := by
      by_contra h; push_neg at h
      rcases lt_or_eq_of_le h with hgt | heq
      · exact hr1 (represents_f_gt_half hf hgt)
      · -- f = 1/2 → round = 0, contradiction
        by_cases hemp : g.empty = true
        · have : f = 0 := by
            obtain ⟨hdd, hxx⟩ : g.digits_ = 0 ∧ g.xbit_ = false := by
              have h' : (g.digits_ == 0 && !g.xbit_) = true := hemp
              rw [Bool.and_eq_true] at h'; exact ⟨beq_iff_eq.mp h'.1, by simpa using h'.2⟩
            exact represents_eq_zero_of_digits_zero_xbit_false hdd hxx hf
          rw [this] at heq; norm_num at heq
        · have hround0 : g.round .to_nearest = 0 :=
            (round_correct (by simpa using hemp) hf).2.2.mpr heq.symm
          exact hr0 hround0
    exact ⟨by omega, hflt⟩
  · -- zm = maxRep + 2: decision always true, contradicting hdec
    exfalso
    have hzeq : zm = 9223372036854775809 := UInt64.toNat_inj.mp (by rw [hz2]; decide)
    have hpo : g.pushOverflow zm .to_nearest = g.push 6 := by
      rw [hzeq]
      unfold Guard.pushOverflow
      rw [if_pos (by decide : maxRep ≤ (9223372036854775809 : UInt64) ∧
        (9223372036854775809 : UInt64) < maxRepUp)]
      simp only [show ((9223372036854775809 : UInt64) % 10 < 9) = false from by decide,
        Bool.false_eq_true, if_false]
      rw [show ((9223372036854775809 : UInt64) == maxRep) = false from by decide, if_neg (by decide),
        show ((9223372036854775809 : UInt64) - maxRep) * 10 / (maxRepUp - maxRep) = 6 from by decide]
    rw [hpo, push6_round_one] at hdec
    simp only [beq_self_eq_true, Bool.true_or] at hdec
    exact absurd hdec (by decide)

/-! ## `RoundsCuspAware` satisfaction for `operator_mul` -/

/-- **`operator_mul` produces a cusp-aware grid image.** For normalized nonzero
factors with a positive product and a nonzero result, the rounded product is
`RoundsCuspAware` of the exact product — the property that makes rounding monotone
across every band, including the cusp exact-tie. -/
theorem operator_mul_roundsCuspAware (x y r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hok : Number.operator_mul x y .to_nearest = .ok r) (hrm : r.mantissa_ ≠ 0)
    (hpos : 0 < x.toRat * y.toRat) :
    r.RoundsCuspAware (x.toRat * y.toRat) := by
  obtain ⟨zm, ze', f, g, res_pos, hF⟩ :=
    operator_mul_algorithmic_facts_to_nearest x y r hx hy hxm hym hok hrm
  set t : ℚ := x.toRat * y.toRat with htdef
  have h10 : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  have ht_val : t = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by
    rw [← abs_of_pos hpos]; exact hF.value_eq
  have hrnn : 0 ≤ r.toRat := mul_result_nonneg_of_truth_pos x y r hF.result_neg hpos
  have hmpos : 0 < (res_pos.mantissa_.toNat : ℚ) := by
    have : res_pos.mantissa_.toNat ≠ 0 := fun h =>
      hF.res_mant_ne (UInt64.toNat_inj.mp (by rw [h]; rfl))
    exact_mod_cast Nat.pos_of_ne_zero this
  have hrpos : 0 < r.toRat := by
    rcases lt_or_eq_of_le hrnn with h | h
    · exact h
    · exfalso; have := hF.result_abs; rw [← h, abs_zero] at this
      have : (0 : ℚ) < (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ :=
        mul_pos hmpos (zpow_pos (by norm_num) _)
      linarith [hF.result_abs ▸ this, h]
  have hr_val : r.toRat = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := by
    rw [← abs_of_pos hrpos]; exact hF.result_abs
  -- fractional facts
  have hf_nn := hF.f_nonneg
  have hf_lt := hF.f_lt_one
  -- f ≤ 1/2 whenever the guard does not decide to round up (regular)
  have hf_le_of_noRU : ¬ g.shouldRoundUp_to_nearest zm → f ≤ 1 / 2 := by
    intro hru
    by_contra h; push_neg at h
    exact hru (Or.inl (represents_f_gt_half hF.represents_f h))
  have hmaxRq : (maxRep.toNat : ℚ) = (maxRepNat : ℚ) := by exact_mod_cast maxRep_val
  have hpow : ∀ e : ℤ, (0 : ℚ) < 10 ^ e := fun e => zpow_pos (by norm_num) e
  have hUpNat : (maxRepUpNat : ℚ) = (maxRepNat : ℚ) + 3 := by norm_num
  by_cases hdir : r.toRat ≤ t
  · -- DOWN
    left
    have hnoinb := operator_mul_no_inbetween_below_to_nearest x y r hx hy hxm hym hok hrm hdir
    obtain ⟨L, hL, hLeq⟩ :=
      operator_mul_rounded_branchA x y r hx hy hxm hym hok hrm hdir hnoinb
    refine ⟨L, hL, hLeq, ?_⟩
    intro U hU
    have closeDown : ∀ (V T zc : ℚ) (e : ℤ), t = zc * 10 ^ e → r.toRat = V * 10 ^ e →
        T * 10 ^ e ≤ U.toRat → 2 * zc ≤ V + T → 2 * t ≤ L.toRat + U.toRat := by
      intro V T zc e htv hV hUb hari
      have hLv : L.toRat = V * 10 ^ e := hLeq ▸ hV
      rw [htv, hLv]
      nlinarith [mul_le_mul_of_nonneg_right hari (le_of_lt (hpow e)), hUb, hpow e]
    by_cases hzm_le_rep : zm.toNat ≤ maxRep.toNat
    · by_cases hru : g.shouldRoundUp_to_nearest zm
      · by_cases hcusp : zm.toNat + 1 ≤ maxRep.toNat
        · -- regular roundUp: value (zm+1)·10^ze' > t, contra DOWN
          exfalso
          have hval := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' hru hcusp
            .overflow res_pos hF.rounds hF.res_mant_ne
          have hV : r.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' := hr_val.trans hval
          rw [hV, ht_val] at hdir
          have := le_of_mul_le_mul_right hdir (hpow ze'); linarith [hf_lt]
        · -- zm = maxRep, roundUp: round = 1 (tie → maxRepUp > t)
          have hzm_eq : zm.toNat = maxRep.toNat := by omega
          have hzmU : zm = maxRep := UInt64.toNat_inj.mp hzm_eq
          have hzmq : (zm.toNat : ℚ) = (maxRepNat : ℚ) := by exact_mod_cast (hzm_eq.trans maxRep_val)
          have hround1 : g.round .to_nearest = 1 := by
            rcases hru with h1 | ⟨h0, hodd⟩
            · exact h1
            · exfalso
              have hval := doRoundUp_value_to_nearest_roundUp_cusp g zm ze' hzmU ⟨h0, hodd⟩
                .overflow res_pos hF.rounds hF.res_mant_ne
              have hV : r.toRat = (maxRepCuspTarget : ℚ) * 10 ^ ze' := hr_val.trans hval
              rw [hV, ht_val] at hdir
              have hc : (maxRepCuspTarget : ℚ) = (zm.toNat : ℚ) + 3 := by rw [hzmq]; norm_num
              rw [hc] at hdir
              have := le_of_mul_le_mul_right hdir (hpow ze'); linarith [hf_lt]
          have hfpos : (0 : ℚ) < f := by
            have := represents_round_eq_one hF.represents_f hround1; linarith
          have hval := doRoundUp_value_to_nearest_roundUp_cusp_round1 g zm ze' hzmU hround1
            .overflow res_pos hF.rounds hF.res_mant_ne
          have hV : r.toRat = (maxRepNat : ℚ) * 10 ^ ze' := by
            rw [hr_val, hval, hmaxRq]
          have hUb : (maxRepUpNat : ℚ) * 10 ^ ze' ≤ U.toRat :=
            upper_ge_cusp_top t U hU ze'
              (by rw [ht_val, hzmq]; exact mul_lt_mul_of_pos_right (by linarith [hfpos]) (hpow ze'))
          exact closeDown (maxRepNat : ℚ) (maxRepUpNat : ℚ) ((zm.toNat : ℚ) + f) ze'
            ht_val hV hUb (by rw [hzmq, hUpNat]; linarith [hf_lt])
      · -- no roundUp: value zm·10^ze', f ≤ 1/2
        have hf_le := hf_le_of_noRU hru
        have hval := doRoundUp_value_no_roundUp g zm ze' hru hzm_le_rep
          .overflow res_pos hF.rounds hF.res_mant_ne
        have hV : r.toRat = (zm.toNat : ℚ) * 10 ^ ze' := hr_val.trans hval
        have hzm_ge : mantissaFloorSucc ≤ zm.toNat := by
          by_contra h; push_neg at h
          have hzf : zm.toNat = mantissaFloor := by have := hF.zm_ge_floor; omega
          have := hF.floor_cusp hzf; linarith [hf_le]
        have hzm_lt : zm.toNat < 10 ^ 19 := by
          have := hF.zm_le_maxRepUp
          rw [show maxRepUp.toNat = maxRepUpNat from rfl] at this; omega
        by_cases hf0 : f = 0
        · have hUb : t ≤ U.toRat := Number.upper_ge t U hU
          have hLv : L.toRat = t := by rw [← hLeq, hV, ht_val, hf0]; ring
          rw [hLv]; linarith [hUb]
        · have hUb : ((zm.toNat : ℚ) + 1) * 10 ^ ze' ≤ U.toRat :=
            upper_ge_cell_top t U hU zm.toNat ze' hzm_ge hzm_lt
              (by rw [ht_val]; have : (0:ℚ) < f := lt_of_le_of_ne hf_nn (Ne.symm hf0)
                  nlinarith [this, hpow ze'])
          exact closeDown (zm.toNat : ℚ) ((zm.toNat : ℚ) + 1) ((zm.toNat : ℚ) + f) ze'
            ht_val hV hUb (by linarith [hf_le])
    · -- zm > maxRep (cusp interior / maxRepUp)
      push_neg at hzm_le_rep
      have hzm_le : zm.toNat ≤ maxRepUp.toNat := hF.zm_le_maxRepUp
      have hzmq_ge : (maxRepNat : ℚ) < (zm.toNat : ℚ) := by
        have : maxRepNat < zm.toNat := by rw [maxRep_val] at hzm_le_rep; exact hzm_le_rep
        exact_mod_cast this
      have hzmq_le : (zm.toNat : ℚ) ≤ (maxRepUpNat : ℚ) := by
        have : zm.toNat ≤ maxRepUpNat := by
          rw [show maxRepUp.toNat = maxRepUpNat from rfl] at hzm_le; exact hzm_le
        exact_mod_cast this
      obtain ⟨v, hvval, hvcases⟩ := doRoundUp_value_cuspRange_cases g zm ze' .to_nearest
        hzm_le_rep hzm_le .overflow res_pos hF.rounds hF.res_mant_ne
      have hrv : r.toRat = (v : ℚ) * 10 ^ ze' := hr_val.trans hvval
      have hA : (0 : ℚ) < 10 ^ ze' := hpow ze'
      rcases hvcases with ⟨hv, hzlt, hdecf⟩ | ⟨hv, hsub⟩ | ⟨hv, hzeqU, _⟩
      · -- v = maxRep (down): zm = maxRep+1, f < 1/2
        obtain ⟨hzm1, hflt⟩ := cusp_interior_down_forces g zm f hF.represents_f hzm_le_rep hzlt hdecf
        have hV : r.toRat = (maxRepNat : ℚ) * 10 ^ ze' := by rw [hrv, hv]
        have hUb : (maxRepUpNat : ℚ) * 10 ^ ze' ≤ U.toRat :=
          upper_ge_cusp_top t U hU ze'
            (by rw [ht_val]; exact mul_lt_mul_of_pos_right (by linarith [hzmq_ge, hf_nn]) hA)
        have hzmq1 : (zm.toNat : ℚ) = (maxRepNat : ℚ) + 1 := by
          exact_mod_cast (show zm.toNat = maxRepNat + 1 from by rw [hzm1, maxRep_val])
        exact closeDown (maxRepNat : ℚ) (maxRepUpNat : ℚ) ((zm.toNat : ℚ) + f) ze'
          ht_val hV hUb (by rw [hzmq1, hUpNat]; linarith [hflt])
      · -- v = maxRepUp
        have hV : r.toRat = (maxRepUpNat : ℚ) * 10 ^ ze' := by rw [hrv, hv, hUpNat]
        rcases hsub with ⟨hzeqU, _⟩ | ⟨hzltU, _⟩
        · -- zm = maxRepUp: coarse cell (maxRepUp, maxRepUp+10)·10^ze'
          have hzmU : (zm.toNat : ℚ) = (maxRepUpNat : ℚ) :=
            by exact_mod_cast (hzeqU.trans (rfl : maxRepUp.toNat = maxRepUpNat))
          by_cases hf0 : f = 0
          · have hUb : t ≤ U.toRat := Number.upper_ge t U hU
            have hLv : L.toRat = t := by rw [← hLeq, hV, ht_val, hzmU, hf0]; ring
            rw [hLv]; linarith [hUb]
          · have hfpos : (0 : ℚ) < f := lt_of_le_of_ne hf_nn (Ne.symm hf0)
            have hUb : (twoPow63Add12 : ℚ) * 10 ^ ze' ≤ U.toRat :=
              upper_ge_coarse_top t U hU ze'
                (by rw [ht_val, hzmU]; exact mul_lt_mul_of_pos_right (by linarith [hfpos]) hA)
            have h12 : (twoPow63Add12 : ℚ) = (maxRepUpNat : ℚ) + 10 := by norm_num
            exact closeDown (maxRepUpNat : ℚ) (twoPow63Add12 : ℚ) ((zm.toNat : ℚ) + f) ze'
              ht_val hV hUb (by rw [hzmU, h12]; linarith [hf_lt])
        · -- zm < maxRepUp: r = maxRepUp·10^ze' > t, contra DOWN
          exfalso
          have hb : (zm.toNat : ℚ) ≤ 9223372036854775809 :=
            by exact_mod_cast (show zm.toNat ≤ 9223372036854775809 from by
              rw [show maxRepUp.toNat = maxRepUpNat from rfl] at hzltU; omega)
          rw [hV, ht_val] at hdir
          have := le_of_mul_le_mul_right hdir hA; rw [hUpNat] at this; linarith [hf_lt, hb]
      · -- v = maxRepNat+13, zm=maxRepUp: a 9-ULP round-up, unreachable for to_nearest via supTight
        exfalso
        have hzmU : (zm.toNat : ℚ) = (maxRepUpNat : ℚ) :=
          by exact_mod_cast (hzeqU.trans (rfl : maxRepUp.toNat = maxRepUpNat))
        have hbound := doRoundUp_rounds_to_nearest_supTight_cusp g zm ze' f hF.represents_f
          hzm_le_rep hzm_le .overflow res_pos hF.rounds hF.res_mant_ne
        rw [hvval, hv, hzmU] at hbound
        have habs : |((maxRepNat : ℚ) + 13) * 10 ^ ze' - ((maxRepUpNat : ℚ) + f) * 10 ^ ze'|
            = (10 - f) * 10 ^ ze' := by
          rw [show ((maxRepNat : ℚ) + 13) * 10 ^ ze' - ((maxRepUpNat : ℚ) + f) * 10 ^ ze'
                = (10 - f) * 10 ^ ze' from by rw [hUpNat]; ring]
          exact abs_of_pos (mul_pos (by linarith [hf_lt]) hA)
        rw [habs] at hbound
        have hden : (((2 ^ 63 + 7 : ℕ)) : ℚ) = 9223372036854775815 := by norm_num
        rw [hden] at hbound
        rw [show ((maxRepUpNat : ℚ) + f) * 10 ^ ze' * (5 / 9223372036854775815)
              = (((maxRepUpNat : ℚ) + f) * (5 / 9223372036854775815)) * 10 ^ ze' from by ring] at hbound
        have hcancel := le_of_mul_le_mul_right hbound hA
        have hrhs : ((maxRepUpNat : ℚ) + f) * (5 / 9223372036854775815) < 6 := by
          rw [← mul_div_assoc, div_lt_iff₀ (by norm_num : (0:ℚ) < 9223372036854775815)]
          nlinarith [hf_lt]
        linarith [hcancel, hrhs, hf_lt]
  · -- UP
    push_neg at hdir
    right
    have hnoinb := operator_mul_no_inbetween_above x y r hx hy hxm hym hok hrm (le_of_lt hdir)
    obtain ⟨U, hU, hUeq⟩ :=
      operator_mul_rounded_branchB x y r hx hy hxm hym hok hrm (le_of_lt hdir) hnoinb
    refine ⟨U, hU, hUeq, ?_⟩
    intro L hL
    have closeUp : ∀ (V B zc : ℚ) (e : ℤ), t = zc * 10 ^ e → U.toRat = V * 10 ^ e →
        L.toRat ≤ B * 10 ^ e → (maxRepNat : ℚ) * (B + V - 2 * zc) < 2 * zc →
        2 * t * ((maxRepNat : ℚ) + 1) > (maxRepNat : ℚ) * (L.toRat + U.toRat) := by
      intro V B zc e htv hUv hLb hcore
      have hmr : (0 : ℚ) ≤ (maxRepNat : ℚ) := by norm_num
      have hle : L.toRat + U.toRat - 2 * t ≤ (B + V - 2 * zc) * 10 ^ e := by
        rw [htv, hUv]; nlinarith [hLb]
      have hstep : (maxRepNat : ℚ) * (L.toRat + U.toRat - 2 * t)
          ≤ (maxRepNat : ℚ) * (B + V - 2 * zc) * 10 ^ e := by
        calc (maxRepNat : ℚ) * (L.toRat + U.toRat - 2 * t)
            ≤ (maxRepNat : ℚ) * ((B + V - 2 * zc) * 10 ^ e) := mul_le_mul_of_nonneg_left hle hmr
          _ = (maxRepNat : ℚ) * (B + V - 2 * zc) * 10 ^ e := by ring
      have hlt : (maxRepNat : ℚ) * (B + V - 2 * zc) * 10 ^ e < 2 * t := by
        have := mul_lt_mul_of_pos_right hcore (hpow e)
        rw [htv]; nlinarith [this]
      have hkey : (maxRepNat : ℚ) * (L.toRat + U.toRat - 2 * t) < 2 * t :=
        lt_of_le_of_lt hstep hlt
      nlinarith [hkey]
    have hzc_pos : ∀ (zc : ℚ) (e : ℤ), t = zc * 10 ^ e → 0 < zc := by
      intro zc e htv
      by_contra h; push_neg at h
      have : t ≤ 0 := by rw [htv]; exact mul_nonpos_of_nonpos_of_nonneg h (le_of_lt (hpow e))
      exact absurd hpos (by rw [htdef] at this ⊢; linarith)
    have closeUpMid : ∀ (V B zc : ℚ) (e : ℤ), t = zc * 10 ^ e → U.toRat = V * 10 ^ e →
        L.toRat ≤ B * 10 ^ e → B + V ≤ 2 * zc →
        2 * t * ((maxRepNat : ℚ) + 1) > (maxRepNat : ℚ) * (L.toRat + U.toRat) := by
      intro V B zc e htv hUv hLb hmid
      refine closeUp V B zc e htv hUv hLb ?_
      have hzc : 0 < zc := hzc_pos zc e htv
      have : (maxRepNat : ℚ) * (B + V - 2 * zc) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith [hmid])
      linarith [hzc, this]
    have hUv0 : U.toRat = r.toRat := hUeq.symm
    by_cases hzm_le_rep : zm.toNat ≤ maxRep.toNat
    · by_cases hcusp : zm.toNat + 1 ≤ maxRep.toNat
      · -- regular: UP forces roundUp; value (zm+1)·10^ze'
        have hru : g.shouldRoundUp_to_nearest zm := by
          by_contra hru
          have hval := doRoundUp_value_no_roundUp g zm ze' hru hzm_le_rep
            .overflow res_pos hF.rounds hF.res_mant_ne
          have hV : r.toRat = (zm.toNat : ℚ) * 10 ^ ze' := hr_val.trans hval
          rw [hV, ht_val] at hdir
          have := lt_of_mul_lt_mul_right hdir (le_of_lt (hpow ze')); linarith [hf_nn]
        have hf_ge : 1 / 2 ≤ f := by
          rcases hru with h1 | ⟨h0, _⟩
          · exact le_of_lt (represents_round_eq_one hF.represents_f h1)
          · exact le_of_eq (represents_round_eq_zero hF.represents_f h0).symm
        have hval := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' hru hcusp
          .overflow res_pos hF.rounds hF.res_mant_ne
        have hV : r.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' := hr_val.trans hval
        have hUv : U.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' := hUv0.trans hV
        by_cases hzm_ge : mantissaFloorSucc ≤ zm.toNat
        · -- fine cell
          have hzm_lt : zm.toNat < 10 ^ 19 := by
            have := hF.zm_le_maxRepUp
            rw [show maxRepUp.toNat = maxRepUpNat from rfl] at this; omega
          have hLb : L.toRat ≤ (zm.toNat : ℚ) * 10 ^ ze' :=
            lower_le_cell_bot t L hL zm.toNat ze' hzm_ge hzm_lt
              (by rw [ht_val]; exact mul_lt_mul_of_pos_right (by linarith [hf_lt]) (hpow ze'))
          exact closeUpMid ((zm.toNat : ℚ) + 1) (zm.toNat : ℚ) ((zm.toNat : ℚ) + f) ze'
            ht_val hUv hLb (by linarith [hf_ge])
        · -- floor band: zm = mantissaFloor, cusp cell at ze'-1
          push_neg at hzm_ge
          have hzf : zm.toNat = mantissaFloor := by have := hF.zm_ge_floor; omega
          have hff : (8 : ℚ) / 10 ≤ f := hF.floor_cusp hzf
          have hzfq : (zm.toNat : ℚ) = (922337203685477580 : ℚ) := by rw [hzf]; norm_num
          have hpowsplit : (10 : ℚ) ^ ze' = 10 ^ (ze' - 1) * 10 := by
            rw [eq_comm, ← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; congr 1; ring
          have htvE : t = ((maxRepNat : ℚ) - 7 + 10 * f) * 10 ^ (ze' - 1) := by
            rw [ht_val, hzfq, hpowsplit]; ring
          have hUvE : U.toRat = (maxRepUpNat : ℚ) * 10 ^ (ze' - 1) := by
            rw [hUv, hzfq, hpowsplit]; ring
          have hLbE : L.toRat ≤ (maxRepNat : ℚ) * 10 ^ (ze' - 1) :=
            lower_le_cusp_bot t L hL (ze' - 1)
              (by rw [htvE]; exact mul_lt_mul_of_pos_right (by linarith [hf_lt, hUpNat]) (hpow (ze' - 1)))
          have hfhcore : (maxRepNat : ℚ) * ((maxRepNat : ℚ) + (maxRepUpNat : ℚ)
              - 2 * ((maxRepNat : ℚ) - 7 + 10 * f)) < 2 * ((maxRepNat : ℚ) - 7 + 10 * f) := by
            have h1 : (maxRepNat : ℚ) * ((maxRepNat : ℚ) + (maxRepUpNat : ℚ)
                - 2 * ((maxRepNat : ℚ) - 7 + 10 * f)) ≤ maxRepNat :=
              mul_le_of_le_one_right (by norm_num) (by linarith [hff, hUpNat])
            linarith [h1, hff]
          exact closeUp (maxRepUpNat : ℚ) (maxRepNat : ℚ) ((maxRepNat : ℚ) - 7 + 10 * f) (ze' - 1)
            htvE hUvE hLbE hfhcore
      · -- zm = maxRep: UP forces round = 0 (tie); value maxRepUp
        have hzm_eq : zm.toNat = maxRep.toNat := by omega
        have hzmU : zm = maxRep := UInt64.toNat_inj.mp hzm_eq
        have hzmq : (zm.toNat : ℚ) = (maxRepNat : ℚ) := by exact_mod_cast (hzm_eq.trans maxRep_val)
        have hround0 : g.round .to_nearest = 0 ∧ zm % 2 = 1 := by
          -- shouldRoundUp holds (UP), and round=1 gives value maxRep ≤ t (DOWN), excluded
          have hru : g.shouldRoundUp_to_nearest zm := by
            by_contra hru
            have hval := doRoundUp_value_no_roundUp g zm ze' hru hzm_le_rep
              .overflow res_pos hF.rounds hF.res_mant_ne
            have hV : r.toRat = (zm.toNat : ℚ) * 10 ^ ze' := hr_val.trans hval
            rw [hV, ht_val] at hdir
            have := lt_of_mul_lt_mul_right hdir (le_of_lt (hpow ze')); linarith [hf_nn]
          rcases hru with h1 | ⟨h0, hodd⟩
          · exfalso
            have hval := doRoundUp_value_to_nearest_roundUp_cusp_round1 g zm ze' hzmU h1
              .overflow res_pos hF.rounds hF.res_mant_ne
            have hV : r.toRat = (maxRepNat : ℚ) * 10 ^ ze' := by rw [hr_val, hval, hmaxRq]
            rw [hV, ht_val, hzmq] at hdir
            have := lt_of_mul_lt_mul_right hdir (le_of_lt (hpow ze')); linarith [hf_nn]
          · exact ⟨h0, hodd⟩
        have hfeq : f = 1 / 2 := represents_round_eq_zero hF.represents_f hround0.1
        have hval := doRoundUp_value_to_nearest_roundUp_cusp g zm ze' hzmU hround0
          .overflow res_pos hF.rounds hF.res_mant_ne
        have hUv : U.toRat = (maxRepUpNat : ℚ) * 10 ^ ze' := by rw [hUv0, hr_val, hval]
        have hLb : L.toRat ≤ (maxRepNat : ℚ) * 10 ^ ze' :=
          lower_le_cusp_bot t L hL ze'
            (by rw [ht_val, hzmq, hfeq]; exact mul_lt_mul_of_pos_right (by linarith [hUpNat]) (hpow ze'))
        have htiehcore : (maxRepNat : ℚ) * ((maxRepNat : ℚ) + (maxRepUpNat : ℚ)
            - 2 * ((zm.toNat : ℚ) + f)) < 2 * ((zm.toNat : ℚ) + f) := by
          rw [hzmq, hfeq, hUpNat]
          have h1 : (maxRepNat : ℚ) + ((maxRepNat : ℚ) + 3) - 2 * ((maxRepNat : ℚ) + 1 / 2) = 2 := by ring
          rw [h1]; norm_num
        exact closeUp (maxRepUpNat : ℚ) (maxRepNat : ℚ) ((zm.toNat : ℚ) + f) ze'
          ht_val hUv hLb htiehcore
    · -- zm > maxRep: cusp interior UP (zm ∈ {maxRep+1, maxRep+2}); value maxRepUp
      push_neg at hzm_le_rep
      have hzm_le : zm.toNat ≤ maxRepUp.toNat := hF.zm_le_maxRepUp
      have hA : (0 : ℚ) < 10 ^ ze' := hpow ze'
      have hzmq_ge : (maxRepNat : ℚ) + 1 ≤ (zm.toNat : ℚ) := by
        have : maxRepNat + 1 ≤ zm.toNat := by rw [maxRep_val] at hzm_le_rep; omega
        exact_mod_cast this
      obtain ⟨v, hvval, hvcases⟩ := doRoundUp_value_cuspRange_cases g zm ze' .to_nearest
        hzm_le_rep hzm_le .overflow res_pos hF.rounds hF.res_mant_ne
      have hrv : r.toRat = (v : ℚ) * 10 ^ ze' := hr_val.trans hvval
      -- the interior closer: from zm < maxRepUp and V = maxRepUp, B = maxRep
      have finishInterior : (zm.toNat : ℚ) ≤ (maxRepNat : ℚ) + 2 →
          r.toRat = (maxRepUpNat : ℚ) * 10 ^ ze' →
          2 * t * ((maxRepNat : ℚ) + 1) > (maxRepNat : ℚ) * (L.toRat + U.toRat) := by
        intro hzlt_q hV
        have hUv : U.toRat = (maxRepUpNat : ℚ) * 10 ^ ze' := hUv0.trans hV
        have hLb : L.toRat ≤ (maxRepNat : ℚ) * 10 ^ ze' :=
          lower_le_cusp_bot t L hL ze'
            (by rw [ht_val]; exact mul_lt_mul_of_pos_right (by linarith [hzlt_q, hf_lt, hUpNat]) hA)
        have hov : (maxRepNat : ℚ) + (maxRepUpNat : ℚ) - 2 * ((zm.toNat : ℚ) + f) ≤ 1 := by
          linarith [hzmq_ge, hf_nn, hUpNat]
        have h1 : (maxRepNat : ℚ) * ((maxRepNat : ℚ) + (maxRepUpNat : ℚ) - 2 * ((zm.toNat : ℚ) + f))
            ≤ maxRepNat := mul_le_of_le_one_right (by norm_num) hov
        exact closeUp (maxRepUpNat : ℚ) (maxRepNat : ℚ) ((zm.toNat : ℚ) + f) ze'
          ht_val hUv hLb (by linarith [h1, hzmq_ge, hf_nn])
      rcases hvcases with ⟨hv, hzlt, _⟩ | ⟨hv, hsub⟩ | ⟨hv, hzeqU, _⟩
      · -- v = maxRep: r ≤ t contradicts UP
        exfalso
        rw [hrv, hv, ht_val] at hdir
        have := lt_of_mul_lt_mul_right hdir (le_of_lt hA)
        linarith [hzmq_ge, hf_nn]
      · -- v = maxRepUp: either zm = maxRepUp (r ≤ t, DOWN, contra) or zm < maxRepUp (proceed)
        rcases hsub with ⟨hzeqU, _⟩ | ⟨hzltU, _⟩
        · exfalso  -- zm = maxRepUp → t ≥ maxRepUp·10^ze' = r, contra UP
          have hzmU : (zm.toNat : ℚ) = (maxRepUpNat : ℚ) :=
            by exact_mod_cast (hzeqU.trans (rfl : maxRepUp.toNat = maxRepUpNat))
          rw [hrv, hv, ht_val, hzmU] at hdir
          have := lt_of_mul_lt_mul_right hdir (le_of_lt hA)
          rw [hUpNat] at this; linarith [hf_nn]
        · have hzlt_q : (zm.toNat : ℚ) ≤ (maxRepNat : ℚ) + 2 := by
            have : zm.toNat ≤ maxRepNat + 2 := by
              rw [show maxRepUp.toNat = maxRepUpNat from rfl] at hzltU; omega
            exact_mod_cast this
          exact finishInterior hzlt_q (by rw [hrv, hv, hUpNat])
      · -- v = maxRepNat+13, zm = maxRepUp: a 9-ULP jump, unreachable for to_nearest via supTight
        exfalso
        have hzmU : (zm.toNat : ℚ) = (maxRepUpNat : ℚ) :=
          by exact_mod_cast (hzeqU.trans (rfl : maxRepUp.toNat = maxRepUpNat))
        have hbound := doRoundUp_rounds_to_nearest_supTight_cusp g zm ze' f hF.represents_f
          hzm_le_rep hzm_le .overflow res_pos hF.rounds hF.res_mant_ne
        rw [hvval, hv, hzmU] at hbound
        have habs : |((maxRepNat : ℚ) + 13) * 10 ^ ze' - ((maxRepUpNat : ℚ) + f) * 10 ^ ze'|
            = (10 - f) * 10 ^ ze' := by
          rw [show ((maxRepNat : ℚ) + 13) * 10 ^ ze' - ((maxRepUpNat : ℚ) + f) * 10 ^ ze'
                = (10 - f) * 10 ^ ze' from by rw [hUpNat]; ring]
          exact abs_of_pos (mul_pos (by linarith [hf_lt]) hA)
        rw [habs] at hbound
        have hden : (((2 ^ 63 + 7 : ℕ)) : ℚ) = 9223372036854775815 := by norm_num
        rw [hden] at hbound
        rw [show ((maxRepUpNat : ℚ) + f) * 10 ^ ze' * (5 / 9223372036854775815)
              = (((maxRepUpNat : ℚ) + f) * (5 / 9223372036854775815)) * 10 ^ ze' from by ring] at hbound
        have hcancel := le_of_mul_le_mul_right hbound hA
        have hrhs : ((maxRepUpNat : ℚ) + f) * (5 / 9223372036854775815) < 6 := by
          rw [← mul_div_assoc, div_lt_iff₀ (by norm_num : (0:ℚ) < 9223372036854775815)]
          nlinarith [hf_lt]
        linarith [hcancel, hrhs, hf_lt]

end XRPL.Model.Protocol
