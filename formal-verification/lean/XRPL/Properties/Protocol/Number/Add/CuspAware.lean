import XRPL.Properties.Protocol.Number.RoundMonotoneCusp
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.RoundedHelpers
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128.RoundFacts

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



/-- Uniform executable nearest-rounding frame for addition.  Same-sign addition
ends in `doRoundUp ... .overflow`; cancellation/different-sign addition ends in
`doNormalize128`'s `doRoundUp ... .normalize2`.  Keeping `loc` in the frame
makes both concrete pipelines feed the same cusp proof without changing either
model branch. -/
structure AddFactsToNearest (x y result : Number)
    (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult) (loc : Error) : Prop where
  zm_ge_floor : mantissaFloor ≤ zm.toNat
  zm_le_maxRepUp : zm.toNat ≤ maxRepUp.toNat
  f_nonneg : 0 ≤ f
  f_lt_one : f < 1
  floor_cusp : zm.toNat = mantissaFloor → (8 : ℚ) / 10 ≤ f
  value_eq : |x.toRat + y.toRat| = ((zm.toNat : ℚ) + f) * 10 ^ ze'
  rounds : g.doRoundUp false zm ze' largeRange.min largeRange.max .to_nearest loc = .ok res_pos
  result_abs : |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_
  res_mant_ne : res_pos.mantissa_ ≠ 0
  result_normalized : result.isNormalized
  round_eq_one : g.round .to_nearest = 1 → f > 1 / 2
  round_eq_zero : g.round .to_nearest = 0 → f = 1 / 2
  f_gt_half : f > 1 / 2 → g.round .to_nearest = 1
  f_eq_half : f = 1 / 2 → g.round .to_nearest = 0
  result_nonneg : 0 < x.toRat + y.toRat → 0 ≤ result.toRat

/-- Addition's two nonzero, noncancelling executable paths expose the common
cusp frame.  The same-sign path supplies the real guard fraction directly;
the different-sign `doNormalize128` path supplies its recovered fraction. -/
theorem operator_add_algorithmic_facts_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    ∃ (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult),
      ∃ loc : Error, AddFactsToNearest x y result zm ze' f g res_pos loc := by
  by_cases h_same : x.negative_ = y.negative_
  · obtain ⟨zm, ze', f, g, res_pos, hzm_ge, hzm_le, hf_nn, hf_lt, hfloor,
      hvalue, hrounds, habs, hres_ne, hrep, hneg, _, _, _⟩ :=
      operator_add_algorithmic_facts_same_sign_to_nearest x y result hx hy
        hx_mant_ne hy_mant_ne h_same h_not_zero hok
    have hnorm : result.isNormalized := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnorm, _⟩ :=
        operator_add_algorithmic_facts_same_sign_to_nearest x y result hx hy
          hx_mant_ne hy_mant_ne h_same h_not_zero hok
      exact hnorm
    have hround1 : g.round .to_nearest = 1 → f > 1 / 2 :=
      fun h => represents_round_eq_one hrep h
    have hround0 : g.round .to_nearest = 0 → f = 1 / 2 :=
      fun h => represents_round_eq_zero hrep h
    have hfgt : f > 1 / 2 → g.round .to_nearest = 1 :=
      fun h => represents_f_gt_half hrep h
    have hfeq : f = 1 / 2 → g.round .to_nearest = 0 := by
      intro h
      by_cases hemp : g.empty = true
      · have hz : f = 0 := by
          obtain ⟨hd, hxbit⟩ : g.digits_ = 0 ∧ g.xbit_ = false := by
            have hh : (g.digits_ == 0 && !g.xbit_) = true := hemp
            rw [Bool.and_eq_true] at hh
            exact ⟨beq_iff_eq.mp hh.1, by simpa using hh.2⟩
          exact represents_eq_zero_of_digits_zero_xbit_false hd hxbit hrep
        exfalso
        linarith [h, hz]
      · exact (round_correct (by simpa using hemp) hrep).2.2.mpr h
    refine ⟨zm, ze', f, g, res_pos, .overflow,
      ⟨hzm_ge, hzm_le, hf_nn, hf_lt, hfloor, hvalue, hrounds, habs,
        hres_ne, hnorm, hround1, hround0, hfgt, hfeq, ?_⟩⟩
    intro hpos
    exact Number.toRat_nonneg_of_nonnegative result
      (hneg.trans (add_same_sign_xn_false_of_truth_pos x y h_same hpos))
  · obtain ⟨M, ze0, δ, zn, sticky, hδ_low, _, hsticky_zero, hM_pos, hM_lt, hM_big,
      htruth, hok128, hsign, hδ_lt, hsticky_pos⟩ :=
      operator_add_algorithmic_facts_diff_sign_represents x y result .to_nearest hx hy
        hx_mant_ne hy_mant_ne h_same h_not_zero hok
    obtain ⟨zm, ze', f, g, res_pos, hzm_ge, hzm_le, hf_nn, hf_lt, hfloor, hvalue,
      hrounds, habs, hres_ne, hneg, _, hround1, hround0, hfgt, hfeq⟩ :=
      doNormalize128_algorithmic_facts_round zn M ze0 δ sticky .to_nearest hδ_low hδ_lt
        hsticky_zero hsticky_pos hM_pos (lt_trans hM_lt (by norm_num))
        (fun hst => by
          have h2 : ((10 : ℚ) ^ 20) ≤ (M.toNat : ℚ) := by exact_mod_cast hM_big hst
          linarith [le_of_lt hδ_lt]) result hok128 hresult
    have hnorm : result.isNormalized :=
      operator_add_result_isNormalized x y result .to_nearest hx hy hx_mant_ne hy_mant_ne
        h_same h_not_zero hok hresult
    refine ⟨zm, ze', f, g, res_pos, .normalize2,
      ⟨hzm_ge, hzm_le, hf_nn, hf_lt, hfloor, htruth.trans hvalue, hrounds, habs,
        hres_ne, hnorm, hround1, hround0, hfgt, hfeq, ?_⟩⟩
    intro hpos
    have hzn : zn = false := zn_eq_false_of_pos hsign.1 hpos
    exact Number.toRat_nonneg_of_nonnegative result (hneg.trans hzn)

/-- Directional lower-neighbour identification for a successful nonzero addition. -/
theorem operator_add_rounded_branchA (x y result : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_not_zero : ¬ x.operator_eq y.operator_neg) (hok : Number.operator_add x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) (hdown : result.toRat ≤ x.toRat + y.toRat) :
    ∃ L, Number.lower (x.toRat + y.toRat) = some L ∧ result.toRat = L.toRat := by
  rcases operator_add_rounded_to_nearest x y result hx hy hok with ⟨L, hL, hr⟩ | ⟨U, hU, hr⟩
  · exact ⟨L, hL, hr⟩
  · rw [hr] at hdown
    have heq : result.toRat = x.toRat + y.toRat := by rw [hr]; exact le_antisymm hdown (Number.upper_ge _ U hU)
    obtain ⟨_, _, _, _, _, _, hF⟩ := operator_add_algorithmic_facts_to_nearest x y result hx hy hx_mant_ne hy_mant_ne h_not_zero hok hresult
    obtain ⟨L, hL, hLval⟩ := Number.lower_value_self result hF.result_normalized (Number.toRat_ne_zero_of_mantissa_ne_zero result hresult)
    rw [heq] at hL
    exact ⟨L, hL, hLval⟩
/-- Directional upper-neighbour identification for a successful nonzero addition. -/
theorem operator_add_rounded_branchB (x y result : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_not_zero : ¬ x.operator_eq y.operator_neg) (hok : Number.operator_add x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) (hup : x.toRat + y.toRat ≤ result.toRat) :
    ∃ U, Number.upper (x.toRat + y.toRat) = some U ∧ result.toRat = U.toRat := by
  rcases operator_add_rounded_to_nearest x y result hx hy hok with ⟨L, hL, hr⟩ | ⟨U, hU, hr⟩
  · rw [hr] at hup
    have heq : result.toRat = x.toRat + y.toRat := by rw [hr]; exact le_antisymm (Number.lower_le _ L hL) hup
    obtain ⟨_, _, _, _, _, _, hF⟩ := operator_add_algorithmic_facts_to_nearest x y result hx hy hx_mant_ne hy_mant_ne h_not_zero hok hresult
    obtain ⟨U, hU, hUval⟩ := Number.upper_value_self result hF.result_normalized (Number.toRat_ne_zero_of_mantissa_ne_zero result hresult)
    rw [heq] at hU
    exact ⟨U, hU, hUval⟩
  · exact ⟨U, hU, hr⟩

lemma doRoundUp_rounds_to_nearest_supTight_cusp_bounds (g : Guard) (zm : UInt64) (ze : Int) (f : ℚ)
    (hf_nn : 0 ≤ f) (hf_lt1 : f < 1)
    (h_zm_gt : maxRep.toNat < zm.toNat)
    (h_zm_le : zm.toNat ≤ maxRepUp.toNat)
    (loc : Error) (res_pos : RoundResult)
    (hok_pos : g.doRoundUp false zm ze largeRange.min largeRange.max .to_nearest loc = .ok res_pos)
    (hres_pos_mant_ne : res_pos.mantissa_ ≠ 0) :
    |(res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ -
       ((zm.toNat : ℚ) + f) * 10 ^ ze|
      ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / (2 ^ 63 + 7 : ℕ)) := by
  have h10ze_pos : (0 : ℚ) < (10 : ℚ) ^ ze := zpow_pos (by norm_num) _
  have h10ze_nn : (0 : ℚ) ≤ (10 : ℚ) ^ ze := le_of_lt h10ze_pos
  have h_denom : (((2 ^ 63 + 7 : ℕ)) : ℚ) = 9223372036854775815 := by push_cast; norm_num
  have hzm_ge_nat : (9223372036854775808 : ℕ) ≤ zm.toNat := by
    rw [maxRep_val] at h_zm_gt; omega
  have hzm_ge_q : (9223372036854775808 : ℚ) ≤ (zm.toNat : ℚ) := by exact_mod_cast hzm_ge_nat
  -- A reusable closer: |E| ≤ 3 suffices against the allowance.
  have h_close : ∀ E : ℚ, |E| ≤ 3 →
      |E| * (10 : ℚ) ^ ze ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ)) := by
    intro E hE
    rw [h_denom]
    rw [show ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / 9223372036854775815)
          = (5 * ((zm.toNat : ℚ) + f) / 9223372036854775815) * 10 ^ ze from by ring]
    apply mul_le_mul_of_nonneg_right _ h10ze_nn
    rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 9223372036854775815)]
    nlinarith [hE, hzm_ge_q, hf_nn]
  unfold Guard.doRoundUp Guard.bringIntoRange at hok_pos
  simp only [Guard.doDropDigit] at hok_pos
  by_cases h_eq_up : zm = maxRepUp
  · -- zm = maxRepUp: pushOverflow no-op; both round paths land on value maxRepUp · 10^ze.
    subst h_eq_up
    have h_pof : g.pushOverflow maxRepUp .to_nearest = g := by
      unfold Guard.pushOverflow
      rw [if_neg]
      intro ⟨_, h⟩
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (lt_irrefl _)
    rw [h_pof] at hok_pos
    have h_not_noncusp : ¬ (maxRepUp < largeRange.max ∧ maxRepUp < maxRep) := by decide
    have h_not_cusp : ¬ (maxRep < maxRepUp ∧ maxRepUp < maxRepUp) := by decide
    have hup_q : ((maxRepUp.toNat : ℕ) : ℚ) = 9223372036854775810 := by
      rw [show maxRepUp.toNat = maxRepUpNat from rfl]; norm_num
    by_cases h_ru : (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1)) = true
    · -- round-up: drop-digit path; pushed-zero guard always rounds down.
      rw [show (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1)) = true
          from h_ru] at hok_pos
      rw [if_pos rfl, if_neg h_not_noncusp, if_neg h_not_cusp] at hok_pos
      have hdig : (g.push (maxRepUp % 10)).digits_.toNat < 5764607523034234880 := by
        have h := toNat_push_digits g (maxRepUp % 10)
        have h0 : (maxRepUp % 10).toNat = 0 := by decide
        rw [h0] at h
        have hlt : g.digits_.toNat < 2 ^ 64 := by
          have hsz := UInt64.toNat_lt_size g.digits_
          rwa [show UInt64.size = 2 ^ 64 from rfl] at hsz
        omega
      have h_ru'_false : ((g.push (maxRepUp % 10)).round .to_nearest == 1
          || ((g.push (maxRepUp % 10)).round .to_nearest == 0 && (maxRepUp / 10) % 2 == 1)) = false := by
        by_cases hemp : (g.push (maxRepUp % 10)).empty = true
        · rw [show (g.push (maxRepUp % 10)).round .to_nearest = -2 from by
            unfold Guard.round; rw [if_pos hemp]]
          rfl
        · rw [round_to_nearest_def hemp]
          have h5 : (0x5000_0000_0000_0000 : UInt64).toNat = 5764607523034234880 := by decide
          have h_not_gt : ¬ ((g.push (maxRepUp % 10)).digits_ > 0x5000_0000_0000_0000) := by
            intro h
            have := UInt64.lt_iff_toNat_lt.mp h
            rw [h5] at this; omega
          have h_lt : (g.push (maxRepUp % 10)).digits_ < 0x5000_0000_0000_0000 := by
            rw [UInt64.lt_iff_toNat_lt, h5]; exact hdig
          rw [if_neg h_not_gt, if_pos h_lt]
          rfl
      rw [show ((g.push (maxRepUp % 10)).round .to_nearest == 1
          || ((g.push (maxRepUp % 10)).round .to_nearest == 0 && (maxRepUp / 10) % 2 == 1)) = false
          from h_ru'_false] at hok_pos
      simp only [Bool.false_eq_true, if_false] at hok_pos
      have h_resc : maxRepUp / 10 < largeRange.min ∧ maxRepUp / 10 ≠ 0 := by decide
      rw [if_pos h_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze + 1 - 1 < minExponent ∨ (maxRepUp / 10) * 10 = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push_neg at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze + 1 - 1 < minExponent ∨ (maxRepUp / 10) * 10 = 0) := by
          push_neg; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze + 1 - 1 > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(((maxRepUp / 10) * 10).toNat : ℚ) * 10 ^ (ze + 1 - 1) -
            ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show ((maxRepUp / 10) * 10).toNat = 9223372036854775810 from by decide,
            show (ze + 1 - 1 : ℤ) = ze from by ring, hup_q,
            show (((9223372036854775810 : ℕ)) : ℚ) = (9223372036854775810 : ℚ) from by norm_num]
        rw [show (9223372036854775810 : ℚ) * 10 ^ ze - (9223372036854775810 + f) * 10 ^ ze
              = -(f * 10 ^ ze) from by ring, abs_neg, abs_mul,
            abs_of_nonneg h10ze_nn, abs_of_nonneg hf_nn]
        have hcf := h_close f (by rw [abs_of_nonneg hf_nn]; linarith)
        rw [abs_of_nonneg hf_nn, hup_q] at hcf
        exact hcf
    · -- no round-up: the no-roundUp cusp test fails; keep maxRepUp.
      rw [Bool.not_eq_true] at h_ru
      rw [show (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1)) = false
          from h_ru] at hok_pos
      simp only [Bool.false_eq_true, if_false] at hok_pos
      rw [if_neg h_not_cusp] at hok_pos
      have h_no_resc : ¬ (maxRepUp < largeRange.min ∧ maxRepUp ≠ 0) := by decide
      rw [if_neg h_no_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze < minExponent ∨ (maxRepUp : UInt64) = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push_neg at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze < minExponent ∨ (maxRepUp : UInt64) = 0) := by
          push_neg; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(maxRepUp.toNat : ℚ) * 10 ^ ze - ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show (maxRepUp.toNat : ℚ) * 10 ^ ze - ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze
              = -(f * 10 ^ ze) from by ring, abs_neg, abs_mul,
            abs_of_nonneg h10ze_nn, abs_of_nonneg hf_nn]
        have := h_close f (by rw [abs_of_nonneg hf_nn]; linarith)
        rw [abs_of_nonneg hf_nn] at this
        exact this
  · -- maxRep < zm < maxRepUp: clamp to maxRepUp (round-up) or maxRep (no round-up).
    have h_lt_up_nat : zm.toNat < maxRepUp.toNat := by
      have hne : zm.toNat ≠ maxRepUp.toNat := fun h => h_eq_up (UInt64.toNat_inj.mp h)
      omega
    have hzm_le_q : (zm.toNat : ℚ) ≤ 9223372036854775809 := by
      exact_mod_cast (by rw [show maxRepUp.toNat = maxRepUpNat from rfl] at h_lt_up_nat
                        ; omega : zm.toNat ≤ 9223372036854775809)
    have h_m_lt_up : zm < maxRepUp := UInt64.lt_iff_toNat_lt.mpr h_lt_up_nat
    have h_maxRep_lt_m : maxRep < zm := UInt64.lt_iff_toNat_lt.mpr h_zm_gt
    have h_cusp_cond : maxRep < zm ∧ zm < maxRepUp := ⟨h_maxRep_lt_m, h_m_lt_up⟩
    have h_not_noncusp : ¬ (zm < largeRange.max ∧ zm < maxRep) := by
      intro ⟨_, h⟩
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (by omega)
    by_cases h_ru : ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
        || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = true
    · -- round-up: clamp up to maxRepUp.
      rw [show ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
          || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = true from h_ru] at hok_pos
      rw [if_pos rfl, if_neg h_not_noncusp, if_pos h_cusp_cond] at hok_pos
      have h_no_resc : ¬ (maxRepUp < largeRange.min ∧ maxRepUp ≠ 0) := by decide
      rw [if_neg h_no_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze < minExponent ∨ (maxRepUp : UInt64) = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push_neg at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze < minExponent ∨ (maxRepUp : UInt64) = 0) := by
          push_neg; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(maxRepUp.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show (maxRepUp.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
              = ((maxRepUp.toNat : ℚ) - (zm.toNat : ℚ) - f) * 10 ^ ze from by ring,
            abs_mul, abs_of_nonneg h10ze_nn]
        apply h_close
        have hup_q : ((maxRepUp.toNat : ℕ) : ℚ) = 9223372036854775810 := by
          rw [show maxRepUp.toNat = maxRepUpNat from rfl]; norm_num
        rw [abs_le]
        constructor
        · rw [hup_q]; linarith
        · rw [hup_q]; linarith
    · -- no round-up: clamp down to maxRep.
      rw [Bool.not_eq_true] at h_ru
      rw [show ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
          || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = false from h_ru] at hok_pos
      simp only [Bool.false_eq_true, if_false] at hok_pos
      rw [if_pos h_cusp_cond] at hok_pos
      have h_no_resc : ¬ (maxRep < largeRange.min ∧ maxRep ≠ 0) := by decide
      rw [if_neg h_no_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze < minExponent ∨ (maxRep : UInt64) = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push_neg at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze < minExponent ∨ (maxRep : UInt64) = 0) := by
          push_neg; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(maxRep.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show (maxRep.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
              = ((maxRep.toNat : ℚ) - (zm.toNat : ℚ) - f) * 10 ^ ze from by ring,
            abs_mul, abs_of_nonneg h10ze_nn]
        apply h_close
        have hrep_q : ((maxRep.toNat : ℕ) : ℚ) = 9223372036854775807 := by
          rw [maxRep_val]; norm_num
        rw [abs_le]
        constructor
        · rw [hrep_q]; linarith
        · rw [hrep_q]; linarith



theorem cusp_interior_down_forces_add (g : Guard) (zm : UInt64) (f : ℚ)
    (hf_gt : f > 1 / 2 → g.round .to_nearest = 1)
    (hf_eq : f = 1 / 2 → g.round .to_nearest = 0)
    (hlo : maxRep.toNat < zm.toNat) (hhi : zm.toNat < maxRepUp.toNat)
    (hdec : ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
       || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = false) :
    zm.toNat = maxRep.toNat + 1 ∧ f < 1 / 2 := by
  have hmaxR : maxRep.toNat = maxRepNat := maxRep_val
  have hmaxRU : maxRepUp.toNat = maxRepUpNat := rfl
  have hcase : zm.toNat = maxRepNat + 1 ∨ zm.toNat = maxRepNat + 2 := by omega
  rcases hcase with hz1 | hz2
  · have hzeq : zm = 9223372036854775808 := UInt64.toNat_inj.mp (by rw [hz1]; decide)
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
    have hnobump : ¬ ((g.round .to_nearest == 1 || g.round .to_nearest == 0) = true) := by
      intro hr
      rw [hpo_bump hr, push6_round_one] at hdec
      simp only [beq_self_eq_true, Bool.true_or] at hdec
      exact absurd hdec (by decide)
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnobump
    obtain ⟨hr1, hr0⟩ := hnobump
    have hflt : f < 1 / 2 := by
      by_contra h; push_neg at h
      rcases lt_or_eq_of_le h with hgt | heq
      · exact hr1 (hf_gt hgt)
      · exact hr0 (hf_eq heq.symm)
    exact ⟨by omega, hflt⟩
  · exfalso
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


private theorem operator_add_roundsCuspAware_nonzero (x y r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hok : Number.operator_add x y .to_nearest = .ok r) (hrm : r.mantissa_ ≠ 0)
    (hpos : 0 < x.toRat + y.toRat) :
    r.RoundsCuspAware (x.toRat + y.toRat) := by
  have h_not_zero : ¬ x.operator_eq y.operator_neg = true := by
    intro heq
    have hzero := add_truth_zero_of_eq_neg x y heq
    linarith
  obtain ⟨zm, ze', f, g, res_pos, loc, hF⟩ :=
    operator_add_algorithmic_facts_to_nearest x y r hx hy hxm hym h_not_zero hok hrm
  set t : ℚ := x.toRat + y.toRat with htdef
  have h10 : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  have ht_val : t = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by
    rw [← abs_of_pos hpos]; exact hF.value_eq
  have hrnn : 0 ≤ r.toRat := hF.result_nonneg hpos
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
    exact hru (Or.inl (hF.f_gt_half h))
  have hmaxRq : (maxRep.toNat : ℚ) = (maxRepNat : ℚ) := by exact_mod_cast maxRep_val
  have hpow : ∀ e : ℤ, (0 : ℚ) < 10 ^ e := fun e => zpow_pos (by norm_num) e
  have hUpNat : (maxRepUpNat : ℚ) = (maxRepNat : ℚ) + 3 := by norm_num
  by_cases hdir : r.toRat ≤ t
  · -- DOWN
    left
    have hnoinb := operator_add_no_inbetween_below_to_nearest x y r hx hy hxm hym h_not_zero hok hrm hdir
    obtain ⟨L, hL, hLeq⟩ :=
      operator_add_rounded_branchA x y r hx hy hxm hym h_not_zero hok hrm hdir
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
            loc res_pos hF.rounds hF.res_mant_ne
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
                loc res_pos hF.rounds hF.res_mant_ne
              have hV : r.toRat = (maxRepCuspTarget : ℚ) * 10 ^ ze' := hr_val.trans hval
              rw [hV, ht_val] at hdir
              have hc : (maxRepCuspTarget : ℚ) = (zm.toNat : ℚ) + 3 := by rw [hzmq]; norm_num
              rw [hc] at hdir
              have := le_of_mul_le_mul_right hdir (hpow ze'); linarith [hf_lt]
          have hfpos : (0 : ℚ) < f := by
            have := hF.round_eq_one hround1; linarith
          have hval := doRoundUp_value_to_nearest_roundUp_cusp_round1 g zm ze' hzmU hround1
            loc res_pos hF.rounds hF.res_mant_ne
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
          loc res_pos hF.rounds hF.res_mant_ne
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
        hzm_le_rep hzm_le loc res_pos hF.rounds hF.res_mant_ne
      have hrv : r.toRat = (v : ℚ) * 10 ^ ze' := hr_val.trans hvval
      have hA : (0 : ℚ) < 10 ^ ze' := hpow ze'
      rcases hvcases with ⟨hv, hzlt, hdecf⟩ | ⟨hv, hsub⟩ | ⟨hv, hzeqU, _⟩
      · -- v = maxRep (down): zm = maxRep+1, f < 1/2
        obtain ⟨hzm1, hflt⟩ := cusp_interior_down_forces_add g zm f hF.f_gt_half hF.f_eq_half hzm_le_rep hzlt hdecf
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
        have hbound := doRoundUp_rounds_to_nearest_supTight_cusp_bounds g zm ze' f hf_nn hf_lt
          hzm_le_rep hzm_le loc res_pos hF.rounds hF.res_mant_ne
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
    have hnoinb := operator_add_no_inbetween_above x y r hx hy hxm hym h_not_zero hok hrm (le_of_lt hdir)
    obtain ⟨U, hU, hUeq⟩ :=
      operator_add_rounded_branchB x y r hx hy hxm hym h_not_zero hok hrm (le_of_lt hdir)
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
            loc res_pos hF.rounds hF.res_mant_ne
          have hV : r.toRat = (zm.toNat : ℚ) * 10 ^ ze' := hr_val.trans hval
          rw [hV, ht_val] at hdir
          have := lt_of_mul_lt_mul_right hdir (le_of_lt (hpow ze')); linarith [hf_nn]
        have hf_ge : 1 / 2 ≤ f := by
          rcases hru with h1 | ⟨h0, _⟩
          · exact le_of_lt (hF.round_eq_one h1)
          · exact le_of_eq (hF.round_eq_zero h0).symm
        have hval := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' hru hcusp
          loc res_pos hF.rounds hF.res_mant_ne
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
              loc res_pos hF.rounds hF.res_mant_ne
            have hV : r.toRat = (zm.toNat : ℚ) * 10 ^ ze' := hr_val.trans hval
            rw [hV, ht_val] at hdir
            have := lt_of_mul_lt_mul_right hdir (le_of_lt (hpow ze')); linarith [hf_nn]
          rcases hru with h1 | ⟨h0, hodd⟩
          · exfalso
            have hval := doRoundUp_value_to_nearest_roundUp_cusp_round1 g zm ze' hzmU h1
              loc res_pos hF.rounds hF.res_mant_ne
            have hV : r.toRat = (maxRepNat : ℚ) * 10 ^ ze' := by rw [hr_val, hval, hmaxRq]
            rw [hV, ht_val, hzmq] at hdir
            have := lt_of_mul_lt_mul_right hdir (le_of_lt (hpow ze')); linarith [hf_nn]
          · exact ⟨h0, hodd⟩
        have hfeq : f = 1 / 2 := hF.round_eq_zero hround0.1
        have hval := doRoundUp_value_to_nearest_roundUp_cusp g zm ze' hzmU hround0
          loc res_pos hF.rounds hF.res_mant_ne
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
        hzm_le_rep hzm_le loc res_pos hF.rounds hF.res_mant_ne
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
        have hbound := doRoundUp_rounds_to_nearest_supTight_cusp_bounds g zm ze' f hf_nn hf_lt
          hzm_le_rep hzm_le loc res_pos hF.rounds hF.res_mant_ne
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


/-- A successful nearest-mode addition with positive exact sum and positive result is a cusp-aware rounding of that exact sum.  Zero operands return exactly, cancellation contradicts positivity, and an underflow flush contradicts the positive result; all remaining executable paths use the verified nonzero bridge. -/
theorem operator_add_roundsCuspAware (x y r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok r)
    (htruth : 0 < x.toRat + y.toRat) (hrpos : 0 < r.toRat) :
    r.RoundsCuspAware (x.toRat + y.toRat) := by
  by_cases hy0 : y.operator_eq Number.zero = true
  · have hyval : y.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero y (Number.mantissa_eq_zero_of_operator_eq_zero hy0)
    have hr : r = x := by unfold Number.operator_add at hok; rw [if_pos hy0] at hok; exact (Except.ok.inj hok).symm
    have hxm : x.mantissa_ ≠ 0 := by intro hm; have h : x.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero x hm; rw [h, hyval] at htruth; norm_num at htruth
    obtain ⟨L, hL, hLval⟩ := Number.lower_value_self x hx (Number.toRat_ne_zero_of_mantissa_ne_zero x hxm)
    left; refine ⟨L, ?_, ?_, ?_⟩
    · rwa [hyval, add_zero]
    · rw [hr]; exact hLval
    · intro U hU; have hUge := Number.upper_ge (x.toRat + y.toRat) U hU; rw [hyval, add_zero] at hUge; rw [hLval]; linarith
  by_cases hx0 : x.operator_eq Number.zero = true
  · have hxval : x.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero x (Number.mantissa_eq_zero_of_operator_eq_zero hx0)
    have hr : r = y := by unfold Number.operator_add at hok; rw [if_neg hy0, if_pos hx0] at hok; exact (Except.ok.inj hok).symm
    have hym : y.mantissa_ ≠ 0 := by intro hm; have h : y.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero y hm; rw [hxval, h] at htruth; norm_num at htruth
    obtain ⟨L, hL, hLval⟩ := Number.lower_value_self y hy (Number.toRat_ne_zero_of_mantissa_ne_zero y hym)
    left; refine ⟨L, ?_, ?_, ?_⟩
    · rwa [hxval, zero_add]
    · rw [hr]; exact hLval
    · intro U hU; have hUge := Number.upper_ge (x.toRat + y.toRat) U hU; rw [hxval, zero_add] at hUge; rw [hLval]; linarith
  by_cases hcancel : x.operator_eq y.operator_neg = true
  · have hzero := add_truth_zero_of_eq_neg x y hcancel; linarith
  have hxm : x.mantissa_ ≠ 0 := by intro hm; apply hx0; rw [Number.eq_zero_of_mantissa_zero x hx hm]; decide
  have hym : y.mantissa_ ≠ 0 := by intro hm; apply hy0; rw [Number.eq_zero_of_mantissa_zero y hy hm]; decide
  have hrm : r.mantissa_ ≠ 0 := by intro hm; have h : r.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero r hm; linarith
  exact operator_add_roundsCuspAware_nonzero x y r hx hy hxm hym hok hrm htruth

end XRPL.Model.Protocol
