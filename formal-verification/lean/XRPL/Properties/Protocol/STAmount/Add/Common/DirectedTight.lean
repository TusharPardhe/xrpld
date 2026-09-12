import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangePos
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangeNeg
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.GridNeighbors

/-! # IOU addition is within **1 ULP** for the directed modes

The directed double rounding (19-digit `Number` sum, then the 16-digit
`IOUAmount.ofNumber` re-round) does not compound: the sum is correctly rounded
(`operator_add_rounded_*`), the re-round is an exact fixed-scale ceiling/floor, and
`Number.upper`/`lower` minimality bounds `result` to within one ULP of the exact sum.
Same argument as `STAmount.Mul.Common.DirectedTight`, split by the sign of the sum. -/

namespace XRPL.Model.Protocol

/-- A nonzero `IOUAmount.ofNumber` result is the raw `normalizeToRange` pair, inside
the IOU offset window. -/
lemma IOUAmount.ofNumber_toRange (n : Number) (mode : rounding_mode) (r : IOUAmount)
    (hok : IOUAmount.ofNumber n mode = .ok r) (hne : r.mantissa_ ≠ 0) :
    n.normalizeToRange cMinValue cMaxValue mode = .ok (r.mantissa_, r.exponent_) ∧
    cMinOffset ≤ r.exponent_ ∧ r.exponent_ ≤ cMaxOffset := by
  unfold IOUAmount.ofNumber IOUAmount.fromNumber at hok
  cases hnr : n.normalizeToRange cMinValue cMaxValue mode with
  | error e => rw [hnr] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨m, e⟩ := me
    rw [hnr] at hok
    simp only at hok
    by_cases hhi : e > cMaxOffset
    · rw [if_pos hhi] at hok; exact absurd hok (by simp)
    · rw [if_neg hhi] at hok
      by_cases hlo2 : e < cMinOffset
      · rw [if_pos hlo2] at hok
        have hz : r = IOUAmount.zero := (Except.ok.inj hok).symm
        rw [hz] at hne
        exact absurd rfl hne
      · rw [if_neg hlo2] at hok
        have hr : (⟨m, e⟩ : IOUAmount) = r := Except.ok.inj hok
        subst hr
        push_neg at hhi hlo2
        exact ⟨rfl, hlo2, hhi⟩

/-- A correctly-rounded nonzero `Number` at a positive target is non-negative. -/
lemma Number.RoundsToRepresentable.nonneg_of_pos (s : Number) (t : ℚ) (mode : rounding_mode)
    (hs : Number.RoundsToRepresentable s t mode) (ht : 0 < t)
    (hpos : 0 < s.mantissa_.toNat) :
    s.negative_ = false := by
  have hlower : ∀ n : Number, Number.lower t = some n → s.toRat = n.toRat → 0 ≤ s.toRat := by
    intro n hlo hval
    have hz := Number.lower_tight t n hlo Number.zero (Or.inl rfl)
      (by rw [Number.toRat_zero]; exact le_of_lt ht)
    rw [Number.toRat_zero] at hz
    rw [hval]; exact hz
  have hupper : ∀ n : Number, Number.upper t = some n → s.toRat = n.toRat → 0 ≤ s.toRat := by
    intro n hup hval
    rw [hval]; exact le_trans (le_of_lt ht) (Number.le_upper t n hup)
  have h0 : 0 ≤ s.toRat := by
    cases mode with
    | to_nearest =>
      rcases hs with ⟨n, hlo, hval⟩ | ⟨n, hup, hval⟩
      · exact hlower n hlo hval
      · exact hupper n hup hval
    | upward => obtain ⟨n, hup, hval⟩ := hs; exact hupper n hup hval
    | downward => obtain ⟨n, hlo, hval⟩ := hs; exact hlower n hlo hval
    | towards_zero =>
      obtain ⟨n, hif, hval⟩ := hs
      rw [if_pos (le_of_lt ht)] at hif
      exact hlower n hif hval
  cases hsn : s.negative_ with
  | false => rfl
  | true =>
    exfalso
    have hm : (0:ℚ) < (s.mantissa_.toNat : ℚ) := by exact_mod_cast hpos
    have hlt : s.toRat < 0 := by
      rw [Number.toRat_of_neg s hsn]
      have := mul_pos hm (zpow_pos (show (0:ℚ) < 10 by norm_num) s.exponent_)
      linarith
    linarith

/-- From a non-negative value and the 16-digit mantissa range: `mant.toInt` casts to a
natural `Mr` with `10^15 ≤ Mr < 10^16`. -/
private lemma directed_grid_facts_pos (mant : Int64) (exp : ℤ)
    (hval_nn : 0 ≤ (mant.toInt : ℚ) * (10 : ℚ) ^ exp)
    (hmr : cMinValue.toNat ≤ mant.toInt.natAbs ∧ mant.toInt.natAbs ≤ cMaxValue.toNat) :
    ∃ Mr : ℕ, (mant.toInt : ℚ) = (Mr : ℚ) ∧ 10 ^ 15 ≤ Mr ∧ Mr < 10 ^ 16 := by
  have hpec : (0:ℚ) < (10:ℚ) ^ exp := zpow_pos (by norm_num) _
  have hmant_nn : 0 ≤ mant.toInt := by
    by_contra hcon
    push_neg at hcon
    have h1 : (mant.toInt : ℚ) < 0 := by exact_mod_cast hcon
    have h2 : (mant.toInt : ℚ) * (10:ℚ) ^ exp < 0 := mul_neg_of_neg_of_pos h1 hpec
    linarith [hval_nn]
  have hnatAbs : mant.toInt.natAbs = mant.toInt.toNat := by omega
  refine ⟨mant.toInt.toNat, ?_, ?_, ?_⟩
  · exact_mod_cast (Int.toNat_of_nonneg hmant_nn).symm
  · have h := hmr.1
    rw [show cMinValue.toNat = 10 ^ 15 from by decide, hnatAbs] at h; exact h
  · have h := hmr.2
    rw [show cMaxValue.toNat = 10 ^ 16 - 1 from by decide, hnatAbs] at h; omega

/-- From a non-positive value and the 16-digit mantissa range: `mant.toInt` casts to
`-Mr` for a natural `Mr` with `10^15 ≤ Mr < 10^16`. -/
private lemma directed_grid_facts_neg (mant : Int64) (exp : ℤ)
    (hval_np : (mant.toInt : ℚ) * (10 : ℚ) ^ exp ≤ 0)
    (hmr : cMinValue.toNat ≤ mant.toInt.natAbs ∧ mant.toInt.natAbs ≤ cMaxValue.toNat) :
    ∃ Mr : ℕ, (mant.toInt : ℚ) = -(Mr : ℚ) ∧ 10 ^ 15 ≤ Mr ∧ Mr < 10 ^ 16 := by
  have hpec : (0:ℚ) < (10:ℚ) ^ exp := zpow_pos (by norm_num) _
  have hmant_np : mant.toInt ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (0:ℚ) < (mant.toInt : ℚ) := by exact_mod_cast hcon
    linarith [mul_pos h1 hpec, hval_np]
  refine ⟨mant.toInt.natAbs, ?_, ?_, ?_⟩
  · have h : mant.toInt = -(mant.toInt.natAbs : ℤ) := by omega
    exact_mod_cast h
  · rw [← show cMinValue.toNat = 10 ^ 15 from by decide]; exact hmr.1
  · have h := hmr.2
    rw [show cMaxValue.toNat = 10 ^ 16 - 1 from by decide] at h; omega

set_option maxHeartbeats 400000 in
-- the per-mode re-rounding and minimality algebra exceeds the default heartbeat budget
/-- **Directed IOU addition of a non-negative exact sum is within 1 ULP.** -/
lemma STAmount.operator_add_repr_iou_directed_core (v1 v2 result : STAmount)
    (mode : rounding_mode)
    (hmode : mode = .upward ∨ mode = .downward ∨ mode = .towards_zero)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (h_truth_nn : 0 ≤ v1.toRat + v2.toRat)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) mode 1 := by
  obtain ⟨xn, yn, sum, sumI, hrv, hexp_br, hofn, hsumI_ne, h_lo, h_hi, he_lo, he_hi,
      hxn_val, hyn_val, hxn_norm, hyn_norm, _hxn_ne, _hyn_ne, _h_no_cancel, hsum_ne, hadd⟩ :=
    STAmount.operator_add_iou_decompose_anyMode v1 v2 result mode hc1 hc2
      h_truth_ne hok hresult
  set truth := v1.toRat + v2.toRat with htruth_def
  have htruth_pos : 0 < truth := lt_of_le_of_ne h_truth_nn (Ne.symm h_truth_ne)
  have hrepr : Number.RoundsToRepresentable sum truth mode := by
    have h : Number.RoundsToRepresentable sum (xn.toRat + yn.toRat) mode := by
      rcases hmode with hm | hm | hm
      · subst hm
        exact operator_add_rounded_upward xn yn sum hxn_norm hyn_norm hadd hsum_ne
      · subst hm
        exact operator_add_rounded_downward xn yn sum hxn_norm hyn_norm hadd hsum_ne
      · subst hm
        exact operator_add_rounded_towards_zero xn yn sum hxn_norm hyn_norm hadd
    rwa [hxn_val, hyn_val] at h
  have hs_neg : sum.negative_ = false :=
    Number.RoundsToRepresentable.nonneg_of_pos sum truth mode hrepr htruth_pos
      (lt_of_lt_of_le (by norm_num) h_lo)
  obtain ⟨hnorm_r, h96, h80⟩ := IOUAmount.ofNumber_toRange sum mode sumI hofn hsumI_ne
  have hmr := normalizeToRange_16_mantissa_range sum mode sumI.mantissa_ sumI.exponent_
    h_lo h_hi he_lo he_hi hnorm_r
  have hres_grid0 : result.toRat = (sumI.mantissa_.toInt : ℚ) * (10 : ℚ) ^ sumI.exponent_ := by
    rw [hrv, IOUAmount.toRat_eq]
  have hres_exp : result.exponent = sumI.exponent_ := hexp_br
  have hsum_val : sum.toRat = (sum.mantissa_.toNat : ℚ) * (10:ℚ) ^ sum.exponent_ :=
    Number.toRat_of_nonneg sum hs_neg
  set M : ℕ := sum.mantissa_.toNat with hM_def
  set mant : Int64 := sumI.mantissa_ with hmant_def
  set exp : ℤ := sumI.exponent_ with hexp_def
  have hp : (0:ℚ) < (10:ℚ) ^ sum.exponent_ := zpow_pos (by norm_num) _
  have h1000 : (10:ℚ) ^ (sum.exponent_ + 3) = (10:ℚ) ^ sum.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ)≠0)]; norm_num
  have hgb_lo : minExponent + 4 ≤ exp := by
    have h := h96; unfold cMinOffset at h; unfold minExponent; omega
  have hgb_hi : exp + 3 ≤ maxExponent := by
    have h := h80; unfold cMaxOffset at h; unfold maxExponent; omega
  rcases hmode with hm | hm | hm
  · -- upward: exact ceiling re-round
    subst hm
    obtain ⟨hval, hEle⟩ := normalizeToRange_16_ceil_pos sum mant exp hs_neg h_lo h_hi
      he_lo he_hi hnorm_r
    set c : ℕ := M / 1000 + (if M % 1000 ≠ 0 then 1 else 0) with hc_def
    have hres_M : result.toRat = (c:ℚ) * 1000 * (10:ℚ)^sum.exponent_ := by
      rw [hres_grid0, hval, h1000]; ring
    have hc_ge : M ≤ c * 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hc_lt : c * 1000 < M + 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hcgeq : (M:ℚ) ≤ (c:ℚ)*1000 := by exact_mod_cast hc_ge
    have hcltq : (c:ℚ)*1000 < (M:ℚ) + 1000 := by exact_mod_cast hc_lt
    have hr_le_res : sum.toRat ≤ result.toRat := by
      rw [hres_M, hsum_val]; nlinarith [hcgeq, hp]
    have hos : result.toRat - sum.toRat < (10:ℚ)^exp := by
      have h1 : result.toRat - sum.toRat < (10:ℚ)^(sum.exponent_+3) := by
        rw [hres_M, hsum_val, h1000]; nlinarith [hcltq, hp]
      have h2 : (10:ℚ)^(sum.exponent_+3) ≤ (10:ℚ)^exp := zpow_le_zpow_right₀ (by norm_num) hEle
      linarith
    obtain ⟨nUp, hup_eq, hsum_eq⟩ := hrepr
    have htruth_le_r : truth ≤ sum.toRat := by
      rw [hsum_eq]; exact Number.le_upper truth nUp hup_eq
    have htruth_le_res : truth ≤ result.toRat := le_trans htruth_le_r hr_le_res
    obtain ⟨Mr, hcast, hmtu_lo, hmtu_hi⟩ :=
      directed_grid_facts_pos mant exp (by rw [hval]; positivity) hmr
    have hres_grid : result.toRat = (Mr:ℚ) * (10:ℚ)^exp := by rw [hres_grid0, hcast]
    have hid : ((Mr:ℚ) - 1) * (10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp - (10:ℚ)^exp := by ring
    obtain ⟨m0, hm0_norm, _hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_below Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have hbelow : ((Mr:ℚ) - 1) * (10:ℚ)^exp ≤ truth := by
      by_contra hcon
      push_neg at hcon
      have hge : truth ≤ m0.toRat := by rw [hm0_val]; linarith
      have hmin := Number.upper_tight truth nUp hup_eq m0 hm0_norm hge
      rw [← hsum_eq, hm0_val] at hmin
      have hcontra : (10:ℚ)^exp ≤ result.toRat - sum.toRat := by
        rw [hres_grid]; linarith [hmin, hid]
      linarith [hos, hcontra]
    refine ⟨htruth_le_res, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonneg (by linarith [htruth_le_res])]
    rw [hres_grid]; linarith [hbelow, hid]
  · -- downward: exact floor re-round
    subst hm
    obtain ⟨hval, hEeq⟩ := normalizeToRange_16_floor_pos sum mant exp .downward (Or.inl rfl)
      hs_neg h_lo h_hi he_lo he_hi hnorm_r
    have hres_M : result.toRat = ((M/1000 : ℕ):ℚ) * 1000 * (10:ℚ)^sum.exponent_ := by
      rw [hres_grid0, hval, h1000]; ring
    have hf_le : (M/1000) * 1000 ≤ M := by omega
    have hf_lt : M < (M/1000) * 1000 + 1000 := by omega
    have hfleq : ((M/1000 : ℕ):ℚ)*1000 ≤ (M:ℚ) := by exact_mod_cast hf_le
    have hfltq : (M:ℚ) < ((M/1000 : ℕ):ℚ)*1000 + 1000 := by exact_mod_cast hf_lt
    have hexpeq : (10:ℚ)^exp = (10:ℚ)^sum.exponent_ * 1000 := by rw [hEeq, h1000]
    have hres_le_r : result.toRat ≤ sum.toRat := by
      rw [hres_M, hsum_val]; nlinarith [hfleq, hp]
    have hos : sum.toRat - result.toRat < (10:ℚ)^exp := by
      rw [hres_M, hsum_val, hexpeq]; nlinarith [hfltq, hp]
    obtain ⟨nLo, hlo_eq, hsum_eq⟩ := hrepr
    have hr_le_truth : sum.toRat ≤ truth := by
      rw [hsum_eq]; exact Number.lower_le truth nLo hlo_eq
    have hres_le_truth : result.toRat ≤ truth := le_trans hres_le_r hr_le_truth
    obtain ⟨Mr, hcast, hmtu_lo, hmtu_hi⟩ :=
      directed_grid_facts_pos mant exp (by rw [hval]; positivity) hmr
    have hres_grid : result.toRat = (Mr:ℚ) * (10:ℚ)^exp := by rw [hres_grid0, hcast]
    have hida : ((Mr:ℚ) + 1) * (10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp + (10:ℚ)^exp := by ring
    obtain ⟨m0, hm0_norm, _hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_above Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have habove : truth ≤ ((Mr:ℚ) + 1) * (10:ℚ)^exp := by
      by_contra hcon
      push_neg at hcon
      have hle : m0.toRat ≤ truth := by rw [hm0_val]; linarith
      have hmax := Number.lower_tight truth nLo hlo_eq m0 hm0_norm hle
      rw [← hsum_eq, hm0_val] at hmax
      have hcontra : (10:ℚ)^exp ≤ sum.toRat - result.toRat := by
        rw [hres_grid]; linarith [hmax, hida]
      linarith [hos, hcontra]
    refine ⟨hres_le_truth, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonpos (by linarith [hres_le_truth]), neg_sub]
    rw [hres_grid]; linarith [habove, hida]
  · -- towards_zero: floor, no directional clause
    subst hm
    obtain ⟨hval, hEeq⟩ := normalizeToRange_16_floor_pos sum mant exp .towards_zero (Or.inr rfl)
      hs_neg h_lo h_hi he_lo he_hi hnorm_r
    have hres_M : result.toRat = ((M/1000 : ℕ):ℚ) * 1000 * (10:ℚ)^sum.exponent_ := by
      rw [hres_grid0, hval, h1000]; ring
    have hf_le : (M/1000) * 1000 ≤ M := by omega
    have hf_lt : M < (M/1000) * 1000 + 1000 := by omega
    have hfleq : ((M/1000 : ℕ):ℚ)*1000 ≤ (M:ℚ) := by exact_mod_cast hf_le
    have hfltq : (M:ℚ) < ((M/1000 : ℕ):ℚ)*1000 + 1000 := by exact_mod_cast hf_lt
    have hexpeq : (10:ℚ)^exp = (10:ℚ)^sum.exponent_ * 1000 := by rw [hEeq, h1000]
    have hres_le_r : result.toRat ≤ sum.toRat := by
      rw [hres_M, hsum_val]; nlinarith [hfleq, hp]
    have hos : sum.toRat - result.toRat < (10:ℚ)^exp := by
      rw [hres_M, hsum_val, hexpeq]; nlinarith [hfltq, hp]
    obtain ⟨nLo, hlo_eq, hsum_eq⟩ := hrepr
    rw [if_pos h_truth_nn] at hlo_eq
    have hr_le_truth : sum.toRat ≤ truth := by
      rw [hsum_eq]; exact Number.lower_le truth nLo hlo_eq
    have hres_le_truth : result.toRat ≤ truth := le_trans hres_le_r hr_le_truth
    obtain ⟨Mr, hcast, hmtu_lo, hmtu_hi⟩ :=
      directed_grid_facts_pos mant exp (by rw [hval]; positivity) hmr
    have hres_grid : result.toRat = (Mr:ℚ) * (10:ℚ)^exp := by rw [hres_grid0, hcast]
    have hida : ((Mr:ℚ) + 1) * (10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp + (10:ℚ)^exp := by ring
    obtain ⟨m0, hm0_norm, _hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_above Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have habove : truth ≤ ((Mr:ℚ) + 1) * (10:ℚ)^exp := by
      by_contra hcon
      push_neg at hcon
      have hle : m0.toRat ≤ truth := by rw [hm0_val]; linarith
      have hmax := Number.lower_tight truth nLo hlo_eq m0 hm0_norm hle
      rw [← hsum_eq, hm0_val] at hmax
      have hcontra : (10:ℚ)^exp ≤ sum.toRat - result.toRat := by
        rw [hres_grid]; linarith [hmax, hida]
      linarith [hos, hcontra]
    refine ⟨trivial, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonpos (by linarith [hres_le_truth]), neg_sub]
    rw [hres_grid]; linarith [habove, hida]

/-- A correctly-rounded nonzero `Number` at a negative target is negative. -/
lemma Number.RoundsToRepresentable.neg_of_neg (s : Number) (t : ℚ) (mode : rounding_mode)
    (hs : Number.RoundsToRepresentable s t mode) (ht : t < 0)
    (hpos : 0 < s.mantissa_.toNat) :
    s.negative_ = true := by
  have hupper : ∀ n : Number, Number.upper t = some n → s.toRat = n.toRat → s.toRat ≤ 0 := by
    intro n hup hval
    have hz := Number.upper_tight t n hup Number.zero (Or.inl rfl)
      (by rw [Number.toRat_zero]; exact le_of_lt ht)
    rw [Number.toRat_zero] at hz
    rw [hval]; exact hz
  have hlower : ∀ n : Number, Number.lower t = some n → s.toRat = n.toRat → s.toRat ≤ 0 := by
    intro n hlo hval
    rw [hval]; exact le_trans (Number.lower_le t n hlo) (le_of_lt ht)
  have h0 : s.toRat ≤ 0 := by
    cases mode with
    | to_nearest =>
      rcases hs with ⟨n, hlo, hval⟩ | ⟨n, hup, hval⟩
      · exact hlower n hlo hval
      · exact hupper n hup hval
    | upward => obtain ⟨n, hup, hval⟩ := hs; exact hupper n hup hval
    | downward => obtain ⟨n, hlo, hval⟩ := hs; exact hlower n hlo hval
    | towards_zero =>
      obtain ⟨n, hif, hval⟩ := hs
      rw [if_neg (not_le.mpr ht)] at hif
      exact hupper n hif hval
  cases hsn : s.negative_ with
  | true => rfl
  | false =>
    exfalso
    have hm : (0:ℚ) < (s.mantissa_.toNat : ℚ) := by exact_mod_cast hpos
    have hgt : 0 < s.toRat := by
      rw [Number.toRat_of_nonneg s hsn]
      exact mul_pos hm (zpow_pos (by norm_num) s.exponent_)
    linarith

set_option maxHeartbeats 400000 in
-- negative mirror: `downward` = magnitude ceiling, `upward`/`towards_zero` = magnitude floor
/-- **Directed IOU addition of a non-positive exact sum is within 1 ULP.** -/
lemma STAmount.operator_add_repr_iou_directed_core_neg (v1 v2 result : STAmount)
    (mode : rounding_mode)
    (hmode : mode = .upward ∨ mode = .downward ∨ mode = .towards_zero)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (h_truth_np : v1.toRat + v2.toRat ≤ 0)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) mode 1 := by
  obtain ⟨xn, yn, sum, sumI, hrv, hexp_br, hofn, hsumI_ne, h_lo, h_hi, he_lo, he_hi,
      hxn_val, hyn_val, hxn_norm, hyn_norm, _hxn_ne, _hyn_ne, _h_no_cancel, hsum_ne, hadd⟩ :=
    STAmount.operator_add_iou_decompose_anyMode v1 v2 result mode hc1 hc2
      h_truth_ne hok hresult
  set truth := v1.toRat + v2.toRat with htruth_def
  have htruth_neg : truth < 0 := lt_of_le_of_ne h_truth_np h_truth_ne
  have hrepr : Number.RoundsToRepresentable sum truth mode := by
    have h : Number.RoundsToRepresentable sum (xn.toRat + yn.toRat) mode := by
      rcases hmode with hm | hm | hm
      · subst hm
        exact operator_add_rounded_upward xn yn sum hxn_norm hyn_norm hadd hsum_ne
      · subst hm
        exact operator_add_rounded_downward xn yn sum hxn_norm hyn_norm hadd hsum_ne
      · subst hm
        exact operator_add_rounded_towards_zero xn yn sum hxn_norm hyn_norm hadd
    rwa [hxn_val, hyn_val] at h
  have hs_neg : sum.negative_ = true :=
    Number.RoundsToRepresentable.neg_of_neg sum truth mode hrepr htruth_neg
      (lt_of_lt_of_le (by norm_num) h_lo)
  obtain ⟨hnorm_r, h96, h80⟩ := IOUAmount.ofNumber_toRange sum mode sumI hofn hsumI_ne
  have hmr := normalizeToRange_16_mantissa_range sum mode sumI.mantissa_ sumI.exponent_
    h_lo h_hi he_lo he_hi hnorm_r
  have hres_grid0 : result.toRat = (sumI.mantissa_.toInt : ℚ) * (10 : ℚ) ^ sumI.exponent_ := by
    rw [hrv, IOUAmount.toRat_eq]
  have hres_exp : result.exponent = sumI.exponent_ := hexp_br
  have hsum_val : sum.toRat = -((sum.mantissa_.toNat : ℚ) * (10:ℚ) ^ sum.exponent_) :=
    Number.toRat_of_neg sum hs_neg
  set M : ℕ := sum.mantissa_.toNat with hM_def
  set mant : Int64 := sumI.mantissa_ with hmant_def
  set exp : ℤ := sumI.exponent_ with hexp_def
  have hp : (0:ℚ) < (10:ℚ) ^ sum.exponent_ := zpow_pos (by norm_num) _
  have h1000 : (10:ℚ) ^ (sum.exponent_ + 3) = (10:ℚ) ^ sum.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ)≠0)]; norm_num
  have hgb_lo : minExponent + 4 ≤ exp := by
    have h := h96; unfold cMinOffset at h; unfold minExponent; omega
  have hgb_hi : exp + 3 ≤ maxExponent := by
    have h := h80; unfold cMaxOffset at h; unfold maxExponent; omega
  rcases hmode with hm | hm | hm
  · -- upward: magnitude floor
    subst hm
    obtain ⟨hval, hEeq⟩ := normalizeToRange_16_floor_neg sum mant exp .upward (Or.inl rfl)
      hs_neg h_lo h_hi he_lo he_hi hnorm_r
    have hres_M : result.toRat = -(((M/1000 : ℕ):ℚ) * 1000 * (10:ℚ)^sum.exponent_) := by
      rw [hres_grid0, hval, h1000]; ring
    have hf_le : (M/1000) * 1000 ≤ M := by omega
    have hf_lt : M < (M/1000) * 1000 + 1000 := by omega
    have hfleq : ((M/1000 : ℕ):ℚ)*1000 ≤ (M:ℚ) := by exact_mod_cast hf_le
    have hfltq : (M:ℚ) < ((M/1000 : ℕ):ℚ)*1000 + 1000 := by exact_mod_cast hf_lt
    have hexpeq : (10:ℚ)^exp = (10:ℚ)^sum.exponent_ * 1000 := by rw [hEeq, h1000]
    obtain ⟨Mr, hcast, hmtu_lo, hmtu_hi⟩ :=
      directed_grid_facts_neg mant exp (by rw [hval, neg_nonpos]; positivity) hmr
    have hres_grid : result.toRat = -((Mr:ℚ) * (10:ℚ)^exp) := by
      rw [hres_grid0, hcast]; ring
    have hr_le_res : sum.toRat ≤ result.toRat := by
      rw [hres_M, hsum_val]; nlinarith [hfleq, hp]
    have hos : result.toRat - sum.toRat < (10:ℚ)^exp := by
      rw [hres_M, hsum_val, hexpeq]; nlinarith [hfltq, hp]
    obtain ⟨nUp, hup_eq, hsum_eq⟩ := hrepr
    have htruth_le_r : truth ≤ sum.toRat := by
      rw [hsum_eq]; exact Number.le_upper truth nUp hup_eq
    have htruth_le_res : truth ≤ result.toRat := le_trans htruth_le_r hr_le_res
    have hidan : -(((Mr:ℚ) + 1) * (10:ℚ)^exp) = -((Mr:ℚ)*(10:ℚ)^exp) - (10:ℚ)^exp := by ring
    obtain ⟨m0, hm0_norm, _hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_above_neg Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have hbelow : -(((Mr:ℚ) + 1) * (10:ℚ)^exp) ≤ truth := by
      by_contra hcon
      push_neg at hcon
      have hge : truth ≤ m0.toRat := by rw [hm0_val]; linarith
      have hmin := Number.upper_tight truth nUp hup_eq m0 hm0_norm hge
      rw [← hsum_eq, hm0_val] at hmin
      have hcontra : (10:ℚ)^exp ≤ result.toRat - sum.toRat := by
        rw [hres_grid]; linarith [hmin, hidan]
      linarith [hos, hcontra]
    refine ⟨htruth_le_res, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonneg (by linarith [htruth_le_res])]
    rw [hres_grid]; linarith [hbelow, hidan]
  · -- downward: magnitude ceiling
    subst hm
    obtain ⟨hval, hEle⟩ := normalizeToRange_16_ceil_neg sum mant exp hs_neg h_lo h_hi
      he_lo he_hi hnorm_r
    set c : ℕ := M / 1000 + (if M % 1000 ≠ 0 then 1 else 0) with hc_def
    have hres_M : result.toRat = -((c:ℚ) * 1000 * (10:ℚ)^sum.exponent_) := by
      rw [hres_grid0, hval, h1000]; ring
    have hc_ge : M ≤ c * 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hc_lt : c * 1000 < M + 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hcgeq : (M:ℚ) ≤ (c:ℚ)*1000 := by exact_mod_cast hc_ge
    have hcltq : (c:ℚ)*1000 < (M:ℚ) + 1000 := by exact_mod_cast hc_lt
    obtain ⟨Mr, hcast, hmtu_lo, hmtu_hi⟩ :=
      directed_grid_facts_neg mant exp (by rw [hval, neg_nonpos]; positivity) hmr
    have hres_grid : result.toRat = -((Mr:ℚ) * (10:ℚ)^exp) := by
      rw [hres_grid0, hcast]; ring
    have hres_le_r : result.toRat ≤ sum.toRat := by
      rw [hres_M, hsum_val]; nlinarith [hcgeq, hp]
    have hos : sum.toRat - result.toRat < (10:ℚ)^exp := by
      have h1 : sum.toRat - result.toRat < (10:ℚ)^(sum.exponent_+3) := by
        rw [hres_M, hsum_val, h1000]; nlinarith [hcltq, hp]
      have h2 : (10:ℚ)^(sum.exponent_+3) ≤ (10:ℚ)^exp := zpow_le_zpow_right₀ (by norm_num) hEle
      linarith
    obtain ⟨nLo, hlo_eq, hsum_eq⟩ := hrepr
    have hr_le_truth : sum.toRat ≤ truth := by
      rw [hsum_eq]; exact Number.lower_le truth nLo hlo_eq
    have hres_le_truth : result.toRat ≤ truth := le_trans hres_le_r hr_le_truth
    have hidn : -(((Mr:ℚ) - 1) * (10:ℚ)^exp) = -((Mr:ℚ)*(10:ℚ)^exp) + (10:ℚ)^exp := by ring
    obtain ⟨m0, hm0_norm, _hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_below_neg Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have habove : truth ≤ -(((Mr:ℚ) - 1) * (10:ℚ)^exp) := by
      by_contra hcon
      push_neg at hcon
      have hle : m0.toRat ≤ truth := by rw [hm0_val]; linarith
      have hmax := Number.lower_tight truth nLo hlo_eq m0 hm0_norm hle
      rw [← hsum_eq, hm0_val] at hmax
      have hcontra : (10:ℚ)^exp ≤ sum.toRat - result.toRat := by
        rw [hres_grid]; linarith [hmax, hidn]
      linarith [hos, hcontra]
    refine ⟨hres_le_truth, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonpos (by linarith [hres_le_truth]), neg_sub]
    rw [hres_grid]; linarith [habove, hidn]
  · -- towards_zero: magnitude floor, no directional clause
    subst hm
    obtain ⟨hval, hEeq⟩ := normalizeToRange_16_floor_neg sum mant exp .towards_zero (Or.inr rfl)
      hs_neg h_lo h_hi he_lo he_hi hnorm_r
    have hres_M : result.toRat = -(((M/1000 : ℕ):ℚ) * 1000 * (10:ℚ)^sum.exponent_) := by
      rw [hres_grid0, hval, h1000]; ring
    have hf_le : (M/1000) * 1000 ≤ M := by omega
    have hf_lt : M < (M/1000) * 1000 + 1000 := by omega
    have hfleq : ((M/1000 : ℕ):ℚ)*1000 ≤ (M:ℚ) := by exact_mod_cast hf_le
    have hfltq : (M:ℚ) < ((M/1000 : ℕ):ℚ)*1000 + 1000 := by exact_mod_cast hf_lt
    have hexpeq : (10:ℚ)^exp = (10:ℚ)^sum.exponent_ * 1000 := by rw [hEeq, h1000]
    obtain ⟨Mr, hcast, hmtu_lo, hmtu_hi⟩ :=
      directed_grid_facts_neg mant exp (by rw [hval, neg_nonpos]; positivity) hmr
    have hres_grid : result.toRat = -((Mr:ℚ) * (10:ℚ)^exp) := by
      rw [hres_grid0, hcast]; ring
    have hr_le_res : sum.toRat ≤ result.toRat := by
      rw [hres_M, hsum_val]; nlinarith [hfleq, hp]
    have hos : result.toRat - sum.toRat < (10:ℚ)^exp := by
      rw [hres_M, hsum_val, hexpeq]; nlinarith [hfltq, hp]
    obtain ⟨nUp, hif, hsum_eq⟩ := hrepr
    rw [if_neg (not_le.mpr htruth_neg)] at hif
    have htruth_le_r : truth ≤ sum.toRat := by
      rw [hsum_eq]; exact Number.le_upper truth nUp hif
    have htruth_le_res : truth ≤ result.toRat := le_trans htruth_le_r hr_le_res
    have hidan : -(((Mr:ℚ) + 1) * (10:ℚ)^exp) = -((Mr:ℚ)*(10:ℚ)^exp) - (10:ℚ)^exp := by ring
    obtain ⟨m0, hm0_norm, _hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_above_neg Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have hbelow : -(((Mr:ℚ) + 1) * (10:ℚ)^exp) ≤ truth := by
      by_contra hcon
      push_neg at hcon
      have hge : truth ≤ m0.toRat := by rw [hm0_val]; linarith
      have hmin := Number.upper_tight truth nUp hif m0 hm0_norm hge
      rw [← hsum_eq, hm0_val] at hmin
      have hcontra : (10:ℚ)^exp ≤ result.toRat - sum.toRat := by
        rw [hres_grid]; linarith [hmin, hidan]
      linarith [hos, hcontra]
    refine ⟨trivial, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonneg (by linarith [htruth_le_res])]
    rw [hres_grid]; linarith [hbelow, hidan]

end XRPL.Model.Protocol
