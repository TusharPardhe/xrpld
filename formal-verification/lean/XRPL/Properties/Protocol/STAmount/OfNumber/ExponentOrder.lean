import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight

/-! # Exponent order for positive fractional `STAmount.ofNumber`

A successful nearest `ofNumber` of a positive normalized `Number` lands on the
16-digit IOU grid at source exponent `+3`, except for the decimal carry cusp,
where it lands at source exponent `+4`.  Thus source value order alone does not
by itself discharge an exponent-order proof from the conversion range facts:
when source exponents coincide, either conversion may occupy either endpoint of
that two-exponent interval.  The exact scale-separation premise for this route is
`n₁.exponent_ + 1 ≤ n₂.exponent_`; it makes the upper endpoint for `n₁` no
larger than the lower endpoint for `n₂`.

This module deliberately states only the fractional protocol fact.  It neither
imports Vault nor assumes that a raw payout is its later clamped debit.
-/

namespace XRPL.Model.Protocol

/-- A positive normalized fractional `Number` converted successfully with
`.to_nearest` has an output exponent in the exact 16-digit snap interval.  The
explicit upper source-range premise is the existing normalizer contract needed
by the snap proof; success-derived discharge of that premise belongs in a
separate boundary layer. -/
lemma STAmount.ofNumber_iou_to_nearest_exponent_bounds
    (n : Number) (result : STAmount)
    (hnorm : n.isNormalized) (hpos : 0 < n.toRat)
    (hrange : n.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok result)
    (hresult : result.mValue ≠ 0) :
    n.exponent_ + 3 ≤ result.exponent ∧ result.exponent ≤ n.exponent_ + 4 := by
  have hmant : n.mantissa_ ≠ 0 := by
    intro hz
    have : n.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero n hz
    linarith
  obtain ⟨hmant_lo, hmant_hi⟩ := hnorm.mantissaBounds_nat hmant
  have hexp_lo : minExponent ≤ n.exponent_ := by
    rcases hnorm with hz | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [hz]; rfl) hmant
    · exact hlo
  have hneg : n.negative_ = false := by
    cases hsign : n.negative_ with
    | false => rfl
    | true =>
      have hnonpos := Number.toRat_nonpos_of_negative n hsign
      linarith
  obtain ⟨mant, exp, hnormed, _, hresult_exp, _, _, _, _, _⟩ :=
    STAmount.ofNumber_iou_snap_pos .fractional n .to_nearest result rfl hneg
      hmant_lo hmant_hi hexp_lo hrange hok hresult
  obtain ⟨hlow, hhigh⟩ := normalizeToRange_16_exp_range n .to_nearest mant exp
    hmant_lo hmant_hi (by omega) hrange hnormed
  rw [hresult_exp]
  exact ⟨hlow, hhigh⟩

/-- The nearest-mode carry cusp is exactly the maximal 16-digit pre-carry
quotient with a dropped three-digit tail of at least `500`.  At the exact half
case the quotient is odd (`10^16 - 1`), so ties round upward. -/
private lemma normalizeToRange_16_nearest_carry_of_max_tail
    (n : Number) (mant : Int64) (exp : Int)
    (hlo : 10 ^ 18 ≤ n.mantissa_.toNat) (hhi : n.mantissa_.toNat < 10 ^ 19)
    (hsrc : minExponent ≤ n.exponent_) (hrange : n.exponent_ + 4 ≤ maxExponent)
    (hnorm : n.normalizeToRange cMinValue cMaxValue .to_nearest = .ok (mant, exp))
    (hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue)
    (htail : 500 ≤ n.mantissa_.toNat % 1000) :
    exp = n.exponent_ + 4 := by
  obtain ⟨g, hrep, _, _, hred⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ .to_nearest hlo hhi
      (by omega) (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hround : (g.round .to_nearest == 1 ||
      (g.round .to_nearest == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true := by
    by_cases hgt : 500 < n.mantissa_.toNat % 1000
    · have hf : (1 / 2 : ℚ) < ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) / 1000 := by
        have : (500 : ℚ) < (n.mantissa_.toNat % 1000 : ℕ) := by exact_mod_cast hgt
        norm_num
        linarith
      have hr : g.round .to_nearest = 1 := represents_f_gt_half hrep hf
      simp [hr]
    · have htail_eq : n.mantissa_.toNat % 1000 = 500 := by omega
      have hf : ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) / 1000 = 1 / 2 := by
        rw [htail_eq]
        norm_num
      have hne : ¬ g.empty := by
        intro he
        simp only [Guard.empty, Guard.unrecoverable, Bool.and_eq_true, beq_iff_eq,
          Bool.not_eq_true'] at he
        obtain ⟨hd, hx⟩ := he
        have hf0 := represents_eq_zero_of_digits_zero_xbit_false hd hx hrep
        rw [hf] at hf0
        norm_num at hf0
      have hr : g.round .to_nearest = 0 := (round_correct hne hrep).2.2.mpr hf
      have hcodd : cMaxValue % 2 = 1 := by decide
      simp [hr, hcusp, hcodd]
  have hcompute : n.normalizeToRange cMinValue cMaxValue .to_nearest
      = .ok (if n.negative_ then -cMinValue.toInt64 else cMinValue.toInt64,
          (n.exponent_ + 3) + 1) := by
    unfold Number.normalizeToRange
    rw [hred, hcusp,
      doRoundUp_small_cusp g n.negative_ (n.exponent_ + 3) .to_nearest .normalize2
        (by rw [hcusp] at hround; exact hround) (by omega) (by omega)]
    rfl
  rw [hcompute] at hnorm
  obtain ⟨_, hexp⟩ := Prod.mk.inj (Except.ok.inj hnorm)
  rw [← hexp]
  omega

/-- A nearest `+4` output can arise only at the carry cusp, and its source tail
is on or above the half-ULP threshold. -/
private lemma normalizeToRange_16_nearest_carry_source
    (n : Number) (mant : Int64) (exp : Int)
    (hlo : 10 ^ 18 ≤ n.mantissa_.toNat) (hhi : n.mantissa_.toNat < 10 ^ 19)
    (hsrc : minExponent ≤ n.exponent_) (hrange : n.exponent_ + 4 ≤ maxExponent)
    (hnorm : n.normalizeToRange cMinValue cMaxValue .to_nearest = .ok (mant, exp))
    (hcarry : exp = n.exponent_ + 4) :
    n.mantissa_ / 10 / 10 / 10 = cMaxValue ∧ 500 ≤ n.mantissa_.toNat % 1000 := by
  obtain ⟨g, hrep, _, _, hred⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ .to_nearest hlo hhi
      (by omega) (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hround : (g.round .to_nearest == 1 ||
      (g.round .to_nearest == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true := by
    by_contra hnot
    have hcompute : n.normalizeToRange cMinValue cMaxValue .to_nearest
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
              else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [hred, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) .to_nearest
        .normalize2 (by simpa using hnot)
        (by rw [hm3, show cMinValue.toNat = 10 ^ 15 by decide]; omega)
        (by rw [hm3, show cMaxValue.toNat = 10 ^ 16 - 1 by decide]; omega)
        (by omega) (by omega)]
      rfl
    rw [hcompute] at hnorm
    obtain ⟨_, hexp⟩ := Prod.mk.inj (Except.ok.inj hnorm)
    omega
  have hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue := by
    by_contra hnot
    have hlt : (n.mantissa_ / 10 / 10 / 10).toNat < cMaxValue.toNat := by
      have hle : (n.mantissa_ / 10 / 10 / 10).toNat ≤ cMaxValue.toNat := by
        rw [hm3, show cMaxValue.toNat = 10 ^ 16 - 1 by decide]
        omega
      exact lt_of_le_of_ne hle (fun h => hnot (UInt64.toNat_inj.mp h))
    have hcompute : n.normalizeToRange cMinValue cMaxValue .to_nearest
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10 + 1).toInt64
              else (n.mantissa_ / 10 / 10 / 10 + 1).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [hred, doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) .to_nearest
        .normalize2 hround
        (by rw [hm3, show cMinValue.toNat = 10 ^ 15 by decide]; omega) hlt
        (by omega) (by omega)]
      rfl
    rw [hcompute] at hnorm
    obtain ⟨_, hexp⟩ := Prod.mk.inj (Except.ok.inj hnorm)
    omega
  refine ⟨hcusp, ?_⟩
  rcases Bool.or_eq_true _ _ |>.mp hround with h1 | h2
  · have hr : g.round .to_nearest = 1 := by simpa using h1
    have hf := represents_round_eq_one hrep hr
    rw [gt_iff_lt, lt_div_iff₀ (by norm_num : (0 : ℚ) < 1000)] at hf
    have : (500 : ℚ) < (n.mantissa_.toNat % 1000 : ℕ) := by linarith
    exact_mod_cast (le_of_lt this)
  · have hr : g.round .to_nearest = 0 := by
      have := (Bool.and_eq_true _ _ |>.mp h2).1
      simpa using this
    have hf := represents_round_eq_zero hrep hr
    rw [div_eq_iff (by norm_num : (1000 : ℚ) ≠ 0)] at hf
    have : n.mantissa_.toNat % 1000 = 500 := by
      exact_mod_cast (by linarith : ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) = 500)
    omega

/-- **Same-source-exponent nearest `ofNumber` exponent order.**  At a shared
source exponent, positive value order is mantissa order.  The only possible
extra output exponent is the carry cusp; its maximal pre-carry quotient and
half-ULP threshold are upward closed, so an earlier carry cannot be reversed by
a later conversion. -/
theorem STAmount.ofNumber_iou_to_nearest_exponent_le_of_same_source_exponent
    (n₁ n₂ : Number) (result₁ result₂ : STAmount)
    (hnorm₁ : n₁.isNormalized) (hnorm₂ : n₂.isNormalized)
    (hpos₁ : 0 < n₁.toRat) (horder : n₁.toRat ≤ n₂.toRat)
    (hexp : n₁.exponent_ = n₂.exponent_)
    (hrange₁ : n₁.exponent_ + 4 ≤ maxExponent)
    (hrange₂ : n₂.exponent_ + 4 ≤ maxExponent)
    (hok₁ : STAmount.ofNumber .fractional n₁ .to_nearest = .ok result₁)
    (hok₂ : STAmount.ofNumber .fractional n₂ .to_nearest = .ok result₂)
    (hresult₁ : result₁.mValue ≠ 0) (hresult₂ : result₂.mValue ≠ 0) :
    result₁.exponent ≤ result₂.exponent := by
  have hpos₂ : 0 < n₂.toRat := lt_of_lt_of_le hpos₁ horder
  have hmant₁ : n₁.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos₁.ne'
  have hmant₂ : n₂.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos₂.ne'
  have hneg₁ : n₁.negative_ = false := by
    cases hs : n₁.negative_ with
    | false => rfl
    | true => exact False.elim (by linarith [Number.toRat_nonpos_of_negative n₁ hs])
  have hneg₂ : n₂.negative_ = false := by
    cases hs : n₂.negative_ with
    | false => rfl
    | true => exact False.elim (by linarith [Number.toRat_nonpos_of_negative n₂ hs])
  obtain ⟨hlo₁, hhi₁⟩ := hnorm₁.mantissaBounds_nat hmant₁
  obtain ⟨hlo₂, hhi₂⟩ := hnorm₂.mantissaBounds_nat hmant₂
  have hsrc_order : n₁.mantissa_.toNat ≤ n₂.mantissa_.toNat := by
    rw [Number.toRat_of_nonneg n₁ hneg₁, Number.toRat_of_nonneg n₂ hneg₂, hexp] at horder
    have hp : (0 : ℚ) < (10 : ℚ) ^ n₂.exponent_ := zpow_pos (by norm_num) _
    have hq : (n₁.mantissa_.toNat : ℚ) ≤ (n₂.mantissa_.toNat : ℚ) :=
      le_of_mul_le_mul_right horder hp
    exact_mod_cast hq
  have hsrc_lo₁ : minExponent ≤ n₁.exponent_ := by
    rcases hnorm₁ with hz | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n₁.mantissa_ = 0 by rw [hz]; rfl) hmant₁
    · exact hlo
  have hsrc_lo₂ : minExponent ≤ n₂.exponent_ := by
    rcases hnorm₂ with hz | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n₂.mantissa_ = 0 by rw [hz]; rfl) hmant₂
    · exact hlo
  obtain ⟨mant₁, exp₁, hnormed₁, _, hres_exp₁, _, _, _, _, _⟩ :=
    STAmount.ofNumber_iou_snap_pos .fractional n₁ .to_nearest result₁ rfl hneg₁
      hlo₁ hhi₁ hsrc_lo₁ hrange₁ hok₁ hresult₁
  obtain ⟨mant₂, exp₂, hnormed₂, _, hres_exp₂, _, _, _, _, _⟩ :=
    STAmount.ofNumber_iou_snap_pos .fractional n₂ .to_nearest result₂ rfl hneg₂
      hlo₂ hhi₂ hsrc_lo₂ hrange₂ hok₂ hresult₂
  have hbound₁ := normalizeToRange_16_exp_range n₁ .to_nearest mant₁ exp₁
    hlo₁ hhi₁ (by omega) hrange₁ hnormed₁
  have hbound₂ := normalizeToRange_16_exp_range n₂ .to_nearest mant₂ exp₂
    hlo₂ hhi₂ (by omega) hrange₂ hnormed₂
  by_cases hcarry : exp₁ = n₁.exponent_ + 4
  · obtain ⟨hcusp₁, htail₁⟩ := normalizeToRange_16_nearest_carry_source n₁ mant₁ exp₁
      hlo₁ hhi₁ hsrc_lo₁ hrange₁ hnormed₁ hcarry
    have hq₁ : n₁.mantissa_.toNat / 1000 = 10 ^ 16 - 1 := by
      have := congrArg UInt64.toNat hcusp₁
      rw [m_div_thousand_toNat, show cMaxValue.toNat = 10 ^ 16 - 1 by decide] at this
      exact this
    have hq₂ : n₂.mantissa_.toNat / 1000 = 10 ^ 16 - 1 := by
      have hdecomp₁ : n₁.mantissa_.toNat / 1000 * 1000 + n₁.mantissa_.toNat % 1000
          = n₁.mantissa_.toNat := by
        have h := Nat.div_add_mod n₁.mantissa_.toNat 1000
        omega
      have hdecomp₂ : n₂.mantissa_.toNat / 1000 * 1000 + n₂.mantissa_.toNat % 1000
          = n₂.mantissa_.toNat := by
        have h := Nat.div_add_mod n₂.mantissa_.toNat 1000
        omega
      omega
    have htail₂ : 500 ≤ n₂.mantissa_.toNat % 1000 := by
      have hdecomp₁ : n₁.mantissa_.toNat / 1000 * 1000 + n₁.mantissa_.toNat % 1000
          = n₁.mantissa_.toNat := by
        have h := Nat.div_add_mod n₁.mantissa_.toNat 1000
        omega
      have hdecomp₂ : n₂.mantissa_.toNat / 1000 * 1000 + n₂.mantissa_.toNat % 1000
          = n₂.mantissa_.toNat := by
        have h := Nat.div_add_mod n₂.mantissa_.toNat 1000
        omega
      omega
    have hcusp₂ : n₂.mantissa_ / 10 / 10 / 10 = cMaxValue := by
      apply UInt64.toNat_inj.mp
      rw [m_div_thousand_toNat, hq₂, show cMaxValue.toNat = 10 ^ 16 - 1 by decide]
    have hcarry₂ : exp₂ = n₂.exponent_ + 4 :=
      normalizeToRange_16_nearest_carry_of_max_tail n₂ mant₂ exp₂ hlo₂ hhi₂ hsrc_lo₂ hrange₂
        hnormed₂ hcusp₂ htail₂
    rw [hres_exp₁, hres_exp₂, hcarry, hcarry₂, hexp]
  · rw [hres_exp₁, hres_exp₂]
    omega

/-- **Scale-separated nearest `ofNumber` exponent order.**  For ordered positive
normalized post-sums, successful fractional `.to_nearest` conversions preserve
output-exponent order whenever the smaller source lies at least one source
decimal exponent below the larger source.  This is exactly the condition that
bridges the possible carry-cusp interval `[e + 3, e + 4]` to the next source
interval `[(e + 1) + 3, (e + 1) + 4]`, as required when comparing dynamic
post-sum grids for `clampToSumExponent`. -/
theorem STAmount.ofNumber_iou_to_nearest_exponent_le_of_source_gap
    (n₁ n₂ : Number) (result₁ result₂ : STAmount)
    (hnorm₁ : n₁.isNormalized) (hnorm₂ : n₂.isNormalized)
    (hpos₁ : 0 < n₁.toRat) (horder : n₁.toRat ≤ n₂.toRat)
    (hgap : n₁.exponent_ + 1 ≤ n₂.exponent_)
    (hrange₁ : n₁.exponent_ + 4 ≤ maxExponent)
    (hrange₂ : n₂.exponent_ + 4 ≤ maxExponent)
    (hok₁ : STAmount.ofNumber .fractional n₁ .to_nearest = .ok result₁)
    (hok₂ : STAmount.ofNumber .fractional n₂ .to_nearest = .ok result₂)
    (hresult₁ : result₁.mValue ≠ 0) (hresult₂ : result₂.mValue ≠ 0) :
    result₁.exponent ≤ result₂.exponent := by
  have hpos₂ : 0 < n₂.toRat := lt_of_lt_of_le hpos₁ horder
  obtain ⟨_, hupper₁⟩ := STAmount.ofNumber_iou_to_nearest_exponent_bounds n₁ result₁
    hnorm₁ hpos₁ hrange₁ hok₁ hresult₁
  obtain ⟨hlower₂, _⟩ := STAmount.ofNumber_iou_to_nearest_exponent_bounds n₂ result₂
    hnorm₂ hpos₂ hrange₂ hok₂ hresult₂
  omega

/-- **Nearest fractional `ofNumber` exponent order from non-strict source-scale
order.**  This is the no-artificial-gap form for post-sum callers: equal source
exponents use the carry-cusp monotonicity theorem, while strictly ordered source
exponents imply the existing one-step scale separation. -/
theorem STAmount.ofNumber_iou_to_nearest_exponent_le_of_source_exponent_le
    (n₁ n₂ : Number) (result₁ result₂ : STAmount)
    (hnorm₁ : n₁.isNormalized) (hnorm₂ : n₂.isNormalized)
    (hpos₁ : 0 < n₁.toRat) (horder : n₁.toRat ≤ n₂.toRat)
    (hsource : n₁.exponent_ ≤ n₂.exponent_)
    (hrange₁ : n₁.exponent_ + 4 ≤ maxExponent)
    (hrange₂ : n₂.exponent_ + 4 ≤ maxExponent)
    (hok₁ : STAmount.ofNumber .fractional n₁ .to_nearest = .ok result₁)
    (hok₂ : STAmount.ofNumber .fractional n₂ .to_nearest = .ok result₂)
    (hresult₁ : result₁.mValue ≠ 0) (hresult₂ : result₂.mValue ≠ 0) :
    result₁.exponent ≤ result₂.exponent := by
  rcases lt_or_eq_of_le hsource with hlt | heq
  · exact STAmount.ofNumber_iou_to_nearest_exponent_le_of_source_gap n₁ n₂ result₁ result₂
      hnorm₁ hnorm₂ hpos₁ horder (by omega) hrange₁ hrange₂ hok₁ hok₂ hresult₁ hresult₂
  · exact STAmount.ofNumber_iou_to_nearest_exponent_le_of_same_source_exponent
      n₁ n₂ result₁ result₂ hnorm₁ hnorm₂ hpos₁ horder heq hrange₁ hrange₂
      hok₁ hok₂ hresult₁ hresult₂

/-- **General nearest fractional `ofNumber` exponent monotonicity.** Ordered,
positive normalized Number inputs determine their source-exponent order from
the canonical 19-digit mantissa bounds. Therefore successful nonzero nearest
fractional conversions preserve output-exponent order without a caller-provided
source exponent relation or artificial scale gap. -/
theorem STAmount.ofNumber_iou_to_nearest_exponent_le_of_normalized_pos_le
    (n₁ n₂ : Number) (result₁ result₂ : STAmount)
    (hnorm₁ : n₁.isNormalized) (hnorm₂ : n₂.isNormalized)
    (hpos₁ : 0 < n₁.toRat) (horder : n₁.toRat ≤ n₂.toRat)
    (hrange₁ : n₁.exponent_ + 4 ≤ maxExponent)
    (hrange₂ : n₂.exponent_ + 4 ≤ maxExponent)
    (hok₁ : STAmount.ofNumber .fractional n₁ .to_nearest = .ok result₁)
    (hok₂ : STAmount.ofNumber .fractional n₂ .to_nearest = .ok result₂)
    (hresult₁ : result₁.mValue ≠ 0) (hresult₂ : result₂.mValue ≠ 0) :
    result₁.exponent ≤ result₂.exponent := by
  exact STAmount.ofNumber_iou_to_nearest_exponent_le_of_source_exponent_le
    n₁ n₂ result₁ result₂ hnorm₁ hnorm₂ hpos₁ horder
    (Number.exponent_le_of_normalized_pos_toRat_le n₁ n₂ hnorm₁ hnorm₂ hpos₁ horder)
    hrange₁ hrange₂ hok₁ hok₂ hresult₁ hresult₂

end XRPL.Model.Protocol
