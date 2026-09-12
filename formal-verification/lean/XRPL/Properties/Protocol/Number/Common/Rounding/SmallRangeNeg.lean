import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangeBound

/-! # Exact 16-digit re-round of a negative `Number`

Mirror of `SmallRangePos`: on the negative side the magnitude roles swap.
`.downward` is the exact magnitude ceiling, `.upward`/`.towards_zero` the exact
magnitude floor. -/

namespace XRPL.Model.Protocol

/-- **`.downward` on a negative `Number`: exact magnitude ceiling**
`-(⌈M/1000⌉·10^(e+3))`, with `exp = e+3` except a `+1` cusp carry. -/
theorem normalizeToRange_16_ceil_neg (n : Number) (mant : Int64) (exp : Int)
    (hnf : n.negative_ = true)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 4 ≤ maxExponent)
    (hok : n.normalizeToRange cMinValue cMaxValue .downward = .ok (mant, exp)) :
    (mant.toInt : ℚ) * 10 ^ exp
      = -(((n.mantissa_.toNat / 1000 + (if n.mantissa_.toNat % 1000 ≠ 0 then 1 else 0) : ℕ) : ℚ)
        * (10 : ℚ) ^ (n.exponent_ + 3))
    ∧ n.exponent_ + 3 ≤ exp := by
  obtain ⟨g, hrep, hsbit, h_empty_of, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ .downward h_lo h_hi he_lo (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  have hmod : n.mantissa_.toNat % 1000 < 1000 := Nat.mod_lt _ (by norm_num)
  have hsb : g.sbit_ = true := by rw [hsbit, hnf]
  by_cases hemp : g.empty = true
  · -- exact (empty guard ⟹ remainder 0): truncate, ceil-div bump is 0.
    have hrem0 : n.mantissa_.toNat % 1000 = 0 := by
      by_contra h
      have hpos : (0 : ℚ) < ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) / 1000 := by
        have : 0 < n.mantissa_.toNat % 1000 := Nat.pos_of_ne_zero h
        positivity
      have := Guard.not_empty_of_represents_pos hrep hpos
      rw [hemp] at this; exact absurd this (by decide)
    have hround : (g.round .downward == 1 || (g.round .downward == 0
        && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = false := round_bool_empty g _ .downward hemp
    have hcompute : n.normalizeToRange cMinValue cMaxValue .downward
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
               else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) .downward
        .normalize2 hround (by rw [hcMin, hm3]; omega) (by rw [hcMax, hm3]; omega)
        (by omega) (by omega)]
      rfl
    rw [hcompute] at hok
    obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
    refine ⟨?_, by omega⟩
    rw [← hmant, ← hexp, signed_mantissa_toInt n.negative_ _ (by rw [hm3]; omega), hm3,
        if_neg (show ¬ n.mantissa_.toNat % 1000 ≠ 0 by rw [hrem0]; decide), hnf, if_pos rfl]
    simp only [neg_mul, one_mul, Int.cast_neg, Int.cast_natCast, Nat.add_zero]
  · -- fire (nonempty ⟹ remainder ≠ 0): magnitude ceil = M/1000 + 1, or cusp carry.
    have hrem_ne : n.mantissa_.toNat % 1000 ≠ 0 := fun h => hemp (h_empty_of h)
    have hround : (g.round .downward == 1 || (g.round .downward == 0
        && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true :=
      round_bool_downward_neg g _ hsb (by simpa using hemp)
    by_cases hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue
    · have hMk : n.mantissa_.toNat / 1000 = 10 ^ 16 - 1 := by
        have := congrArg UInt64.toNat hcusp; rw [hm3, hcMax] at this; exact this
      have hcompute : n.normalizeToRange cMinValue cMaxValue .downward
          = .ok (if n.negative_ then -cMinValue.toInt64 else cMinValue.toInt64, (n.exponent_ + 3) + 1) := by
        unfold Number.normalizeToRange
        rw [h_red, hcusp, doRoundUp_small_cusp g n.negative_ (n.exponent_ + 3) .downward
          .normalize2 (by rw [hcusp] at hround; exact hround) (by omega) (by omega)]
        rfl
      rw [hcompute] at hok
      obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
      refine ⟨?_, by omega⟩
      rw [← hmant, ← hexp, signed_mantissa_toInt n.negative_ cMinValue (by rw [hcMin]; omega),
          if_pos hrem_ne, hMk, hnf, if_pos rfl, hcMin,
          show ((10 ^ 16 - 1 + 1 : ℕ)) = (10 ^ 16 : ℕ) from by norm_num,
          zpow_add₀ (by norm_num : (10:ℚ) ≠ 0) (n.exponent_ + 3) 1, zpow_one]
      push_cast; ring
    · have hlt : (n.mantissa_ / 10 / 10 / 10).toNat < cMaxValue.toNat := by
        have hne : (n.mantissa_ / 10 / 10 / 10).toNat ≠ cMaxValue.toNat :=
          fun h => hcusp (UInt64.toNat_inj.mp h)
        rw [hcMax, hm3] at hne ⊢; omega
      have hadd : (n.mantissa_ / 10 / 10 / 10 + 1).toNat = n.mantissa_.toNat / 1000 + 1 := by
        rw [UInt64.toNat_add, hm3, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      have hcompute : n.normalizeToRange cMinValue cMaxValue .downward
          = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10 + 1).toInt64
                 else (n.mantissa_ / 10 / 10 / 10 + 1).toInt64, n.exponent_ + 3) := by
        unfold Number.normalizeToRange
        rw [h_red, doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) .downward
          .normalize2 hround (by rw [hcMin, hm3]; omega) hlt (by omega) (by omega)]
        rfl
      rw [hcompute] at hok
      obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
      refine ⟨?_, by omega⟩
      rw [← hmant, ← hexp, signed_mantissa_toInt n.negative_ _ (by rw [hadd]; omega), hadd,
          if_pos hrem_ne, hnf, if_pos rfl]
      simp only [neg_mul, one_mul, Int.cast_neg, Int.cast_natCast]

/-- **`.upward`/`.towards_zero` on a negative `Number`: exact magnitude floor**
`-(⌊M/1000⌋·10^(e+3))` at `exp = e+3`. -/
theorem normalizeToRange_16_floor_neg (n : Number) (mant : Int64) (exp : Int) (mode : rounding_mode)
    (hmode : mode = .upward ∨ mode = .towards_zero)
    (hnf : n.negative_ = true)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 4 ≤ maxExponent)
    (hok : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    (mant.toInt : ℚ) * 10 ^ exp
      = -(((n.mantissa_.toNat / 1000 : ℕ) : ℚ) * (10 : ℚ) ^ (n.exponent_ + 3))
    ∧ exp = n.exponent_ + 3 := by
  obtain ⟨g, hrep, hsbit, h_empty_of, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ mode h_lo h_hi he_lo (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  have hsb : g.sbit_ = true := by rw [hsbit, hnf]
  have hround : (g.round mode == 1 || (g.round mode == 0
      && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = false := by
    rcases hmode with h | h
    · rw [h]; exact round_bool_upward_neg g _ hsb
    · rw [h]; exact round_bool_towards_zero g _
  have hcompute : n.normalizeToRange cMinValue cMaxValue mode
      = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
             else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
    unfold Number.normalizeToRange
    rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) mode
      .normalize2 hround (by rw [hcMin, hm3]; omega) (by rw [hcMax, hm3]; omega)
      (by omega) (by omega)]
    rfl
  rw [hcompute] at hok
  obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
  refine ⟨?_, by omega⟩
  rw [← hmant, ← hexp, signed_mantissa_toInt n.negative_ _ (by rw [hm3]; omega), hm3,
      hnf, if_pos rfl]
  simp only [neg_mul, one_mul, Int.cast_neg, Int.cast_natCast]

end XRPL.Model.Protocol
