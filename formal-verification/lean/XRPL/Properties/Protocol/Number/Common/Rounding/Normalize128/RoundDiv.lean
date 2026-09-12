import Mathlib.Tactic

import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128
import XRPL.Properties.Protocol.Number.Common.Constants

namespace XRPL.Model.Protocol

/-! # Exact value-fraction / round agreement for `doNormalize128`

The `doNormalize128` staged pipeline (used by `operator_div`) tracks the dropped
digits in a `Guard`, but the standard `represents g ftilde` characterization only
pins a coarse shadow `ftilde` of the true value fraction `f`. For the
round-to-nearest decision we need the guard's `round` output to agree with the
*true* fraction `f ⋛ 1/2`.

`decimalValue g.digits_` captures the top `p` dropped decimal digits of `f`
exactly, with a bounded tail: `f = decimalValue g.digits_ / 10^16 + x`,
`0 ≤ x < 1/10^p`, `xbit ↔ x > 0`, and `decimalValue g.digits_ · 10^p` divisible by
`10^16`. From this the guard's `round` value coincides with `f ⋛ 1/2`. -/

/-! ## Nibble-0 helpers -/

/-- The sum of positions `1..15` of `decimalValue` is divisible by `10`. -/
lemma ten_dvd_decimalValue_tail (d : UInt64) :
    10 ∣ ∑ p ∈ Finset.range 15, nibble d (p + 1) * 10 ^ (p + 1) := by
  apply Finset.dvd_sum
  intro p _
  exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) _

/-- `decimalValue d ≡ nibble d 0 (mod 10)` (as `decimalValue d % 10 = nibble d 0`
for a valid decimal guard). -/
lemma decimalValue_mod_ten (d : UInt64) (hall : allNibblesAtMost9 d) :
    decimalValue d % 10 = nibble d 0 := by
  have hsplit : decimalValue d
      = nibble d 0 + ∑ p ∈ Finset.range 15, nibble d (p + 1) * 10 ^ (p + 1) := by
    unfold decimalValue
    rw [Finset.sum_range_succ' (fun p => nibble d p * 10 ^ p) 15]
    simp [pow_zero, Nat.add_comm]
  obtain ⟨k, hk⟩ := ten_dvd_decimalValue_tail d
  have hnib : nibble d 0 ≤ 9 := hall ⟨0, by omega⟩
  rw [hsplit, hk]; omega

/-- If `10 ∣ decimalValue d`, the bottom nibble is zero. -/
lemma nibble_zero_of_ten_dvd (d : UInt64) (hall : allNibblesAtMost9 d)
    (hdvd : 10 ∣ decimalValue d) : nibble d 0 = 0 := by
  rw [← decimalValue_mod_ten d hall]; omega

/-- `allNibblesAtMost9` is preserved by `push` of a decimal digit. -/
lemma allNibblesAtMost9_push (g : Guard) (d : UInt64) (hd : d.toNat < 10)
    (hall : allNibblesAtMost9 g.digits_) :
    allNibblesAtMost9 (g.push d).digits_ := by
  have d_eq : d.toNat % 16 = d.toNat := Nat.mod_eq_of_lt (by omega)
  intro q
  by_cases hp : q.val < 15
  · rw [nibble_push_lt hp]; exact hall ⟨q.val + 1, by omega⟩
  · have hp15 : q.val = 15 := by omega
    rw [hp15, nibble_push_top, d_eq]; omega

/-! ## The enriched scale-down invariant -/

set_option maxHeartbeats 1000000 in
-- Heavy functional-induction over `doNormalize_scaleDown128` with per-step ℚ algebra.
/-- Value/digit invariant threaded through `doNormalize_scaleDown128`. The output
fraction `φ'` decomposes exactly against the accumulated guard, with the tail `x'`
below the captured `p'` digits, and the captured digits sitting in the top nibbles
(`10^16 ∣ decimalValue · 10^p'`). The `size` conjunct bounds the push count. -/
theorem doNormalize_scaleDown128_valueInv
    (maxMantissa : UInt64) (m : UInt128) (e : Int) (g : Guard)
    (hmaxM : maxMantissa.toNat = 9999999999999999999)
    (φ x : ℚ) (p : ℕ)
    (hx_nn : 0 ≤ x) (hx_lt : x < 1 / 10 ^ p)
    (hval : φ = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)
    (hxbit : g.xbit_ = true ↔ 0 < x)
    (hall : allNibblesAtMost9 g.digits_)
    (hdvd : (10 : ℕ) ^ 16 ∣ decimalValue g.digits_ * 10 ^ p)
    (hsize : m.toNat * 10 ^ p < 10 ^ 23)
    (hcouple : x * 10 ^ 20 ≤ (m.toNat : ℚ) * 10 ^ p)
    (out : UInt128 × Int × Guard)
    (hok : doNormalize_scaleDown128 maxMantissa m e g = .ok out) :
    ∃ (φ' x' : ℚ) (p' : ℕ),
      0 ≤ x' ∧ x' < 1 / 10 ^ p' ∧
      φ' = (decimalValue out.2.2.digits_ : ℚ) / 10 ^ 16 + x' ∧
      (out.2.2.xbit_ = true ↔ 0 < x') ∧
      allNibblesAtMost9 out.2.2.digits_ ∧
      (10 : ℕ) ^ 16 ∣ decimalValue out.2.2.digits_ * 10 ^ p' ∧
      out.1.toNat * 10 ^ p' < 10 ^ 23 ∧
      x' * 10 ^ 20 ≤ (out.1.toNat : ℚ) * 10 ^ p' ∧
      ((m.toNat : ℚ) + φ) * 10 ^ e = ((out.1.toNat : ℚ) + φ') * 10 ^ out.2.1 := by
  induction m, e, g using doNormalize_scaleDown128.induct (maxMantissa := maxMantissa)
    generalizing φ x p with
  | case1 m e g hgt hge =>
    rw [show doNormalize_scaleDown128 maxMantissa m e g = .error .normalize1 from by
      rw [doNormalize_scaleDown128.eq_def, dif_pos hgt, if_pos hge]] at hok
    exact absurd hok (by intro h; cases h)
  | case2 m e g hgt hnge ih =>
    rw [show doNormalize_scaleDown128 maxMantissa m e g
        = doNormalize_scaleDown128 maxMantissa (m / 10) (e + 1) (g.push (toUInt64 (m % 10)))
        from by rw [doNormalize_scaleDown128.eq_def, dif_pos hgt, if_neg hnge]] at hok
    have h10 : ((10 : UInt128)).toNat = 10 := by decide
    have h_div : (m / 10 : UInt128).toNat = m.toNat / 10 := by rw [BitVec.toNat_udiv, h10]
    have h_mod : (m % 10 : UInt128).toNat = m.toNat % 10 := by rw [BitVec.toNat_umod, h10]
    have h_d_toNat : (toUInt64 (m % 10)).toNat = m.toNat % 10 := by
      rw [toNat_toUInt64 (by rw [h_mod]; have : m.toNat % 10 < 10 := Nat.mod_lt _ (by norm_num); omega), h_mod]
    have h_d_lt : (toUInt64 (m % 10)).toNat < 10 := by rw [h_d_toNat]; exact Nat.mod_lt _ (by norm_num)
    have hgt_nat : maxMantissa.toNat < m.toNat := by
      have := BitVec.lt_def.mp hgt
      rwa [toNat_toUInt128] at this
    have hm_ge : (10 : ℕ) ^ 19 ≤ m.toNat := by rw [hmaxM] at hgt_nat; omega
    have hp_le : p ≤ 3 := by
      by_contra hpc
      push_neg at hpc
      have h1 : (10 : ℕ) ^ 19 * 10 ^ p < 10 ^ 23 := lt_of_le_of_lt (Nat.mul_le_mul_right _ hm_ge) hsize
      have h2 : (10 : ℕ) ^ 23 ≤ 10 ^ 19 * 10 ^ p := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdvd10 : 10 ∣ decimalValue g.digits_ := by
      have hsplit : (10 : ℕ) ^ 16 = 10 ^ (16 - p) * 10 ^ p := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit] at hdvd
      have hstep : (10 : ℕ) ^ (16 - p) ∣ decimalValue g.digits_ :=
        (Nat.mul_dvd_mul_iff_right (by positivity)).mp hdvd
      exact (dvd_pow_self 10 (show 16 - p ≠ 0 by omega)).trans hstep
    have hnib0 : nibble g.digits_ 0 = 0 := nibble_zero_of_ten_dvd g.digits_ hall hdvd10
    -- recursive-call invariant
    have hx'_nn : (0 : ℚ) ≤ x / 10 := by positivity
    have hx'_lt : x / 10 < 1 / 10 ^ (p + 1) := by
      have hp : (0 : ℚ) < 10 ^ p := by positivity
      have hxp : x * 10 ^ p < 1 := (lt_div_iff₀ hp).mp hx_lt
      rw [pow_succ, div_lt_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hxp, hp]
    have hval' : (φ + ((toUInt64 (m % 10)).toNat : ℚ)) / 10
        = (decimalValue (g.push (toUInt64 (m % 10))).digits_ : ℚ) / 10 ^ 16 + x / 10 := by
      have hf := represents_push_formula (toUInt64 (m % 10)) h_d_lt φ hval
      rw [hf, hnib0]; push_cast; ring
    have hxbit' : (g.push (toUInt64 (m % 10))).xbit_ = true ↔ 0 < x / 10 := by
      have h := represents_push_xbit (toUInt64 (m % 10)) hx_nn hxbit
      rw [hnib0] at h; simpa using h
    have hall' : allNibblesAtMost9 (g.push (toUInt64 (m % 10))).digits_ :=
      allNibblesAtMost9_push g _ h_d_lt hall
    have hdvd' : (10 : ℕ) ^ 16 ∣ decimalValue (g.push (toUInt64 (m % 10))).digits_ * 10 ^ (p + 1) := by
      -- 10·decimalValue(push) = decimalValue + d·10^16 - nibble0, and nibble0 = 0
      have hpr := decimalValue_push g (toUInt64 (m % 10))
      rw [hnib0, Nat.add_zero] at hpr
      have hd_eq : (toUInt64 (m % 10)).toNat % 16 = (toUInt64 (m % 10)).toNat :=
        Nat.mod_eq_of_lt (by omega)
      rw [hd_eq] at hpr
      -- hpr : 10 * decimalValue (push) = decimalValue g + d * 10^16
      have key : decimalValue (g.push (toUInt64 (m % 10))).digits_ * 10 ^ (p + 1)
          = decimalValue g.digits_ * 10 ^ p + (toUInt64 (m % 10)).toNat * 10 ^ 16 * 10 ^ p := by
        have : 10 * decimalValue (g.push (toUInt64 (m % 10))).digits_ * 10 ^ p
            = (decimalValue g.digits_ + (toUInt64 (m % 10)).toNat * 10 ^ 16) * 10 ^ p := by
          rw [hpr]
        rw [pow_succ]
        calc decimalValue (g.push (toUInt64 (m % 10))).digits_ * (10 ^ p * 10)
            = 10 * decimalValue (g.push (toUInt64 (m % 10))).digits_ * 10 ^ p := by ring
          _ = (decimalValue g.digits_ + (toUInt64 (m % 10)).toNat * 10 ^ 16) * 10 ^ p := this
          _ = decimalValue g.digits_ * 10 ^ p + (toUInt64 (m % 10)).toNat * 10 ^ 16 * 10 ^ p := by ring
      rw [key]
      exact Nat.dvd_add hdvd (by rw [show (toUInt64 (m % 10)).toNat * 10 ^ 16 * 10 ^ p
        = 10 ^ 16 * ((toUInt64 (m % 10)).toNat * 10 ^ p) from by ring]; exact Dvd.intro _ rfl)
    have hsize' : (m / 10 : UInt128).toNat * 10 ^ (p + 1) < 10 ^ 23 := by
      rw [h_div, pow_succ]
      calc m.toNat / 10 * (10 ^ p * 10) = (m.toNat / 10 * 10) * 10 ^ p := by ring
        _ ≤ m.toNat * 10 ^ p := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
        _ < 10 ^ 23 := hsize
    have hcouple' : (x / 10) * 10 ^ 20 ≤ ((m / 10 : UInt128).toNat : ℚ) * 10 ^ (p + 1) := by
      have hP : (0 : ℚ) < 10 ^ p := by positivity
      have hkey : (m.toNat : ℚ) ≤ ((m.toNat / 10 : ℕ) : ℚ) * 100 := by
        exact_mod_cast (show m.toNat ≤ m.toNat / 10 * 100 by omega)
      rw [h_div, show (x / 10) * 10 ^ 20 = (x * 10 ^ 20) / 10 from by ring,
          div_le_iff₀ (by norm_num : (0:ℚ) < 10), pow_succ 10 p]
      calc x * 10 ^ 20 ≤ (m.toNat : ℚ) * 10 ^ p := hcouple
        _ ≤ ((m.toNat / 10 : ℕ) : ℚ) * 100 * 10 ^ p := mul_le_mul_of_nonneg_right hkey hP.le
        _ = ((m.toNat / 10 : ℕ) : ℚ) * (10 ^ p * 10) * 10 := by ring
    obtain ⟨φ', x', p', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      ih ((φ + ((toUInt64 (m % 10)).toNat : ℚ)) / 10) (x / 10) (p + 1)
        hx'_nn hx'_lt hval' hxbit' hall' hdvd' hsize' hcouple' hok
    refine ⟨φ', x', p', h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
    -- value equation
    rw [← h9]
    have h_decomp : (m.toNat : ℚ) = ((m / 10 : UInt128).toNat : ℚ) * 10
        + ((toUInt64 (m % 10)).toNat : ℚ) := by
      rw [h_div, h_d_toNat]
      have h_nat : m.toNat = m.toNat / 10 * 10 + m.toNat % 10 := by omega
      have h_q : (m.toNat : ℚ) = ((m.toNat / 10 * 10 + m.toNat % 10 : ℕ) : ℚ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) h_nat
      rw [h_q]; push_cast; ring
    rw [h_decomp, show (10 : ℚ) ^ (e + 1) = 10 ^ e * 10 from by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp]
    field_simp
    ring
  | case3 m e g hgt =>
    rw [show doNormalize_scaleDown128 maxMantissa m e g = .ok (m, e, g) from by
      rw [doNormalize_scaleDown128.eq_def, dif_neg hgt]] at hok
    obtain rfl := (Except.ok.inj hok).symm
    exact ⟨φ, x, p, hx_nn, hx_lt, hval, hxbit, hall, hdvd, hsize, hcouple, by ring⟩

/-- Same value/digit invariant threaded through `doNormalize_capAtMaxRep` (at most
one push). -/
theorem doNormalize_capAtMaxRep_valueInv
    (m : UInt64) (e : Int) (g : Guard)
    (φ x : ℚ) (p : ℕ)
    (hx_nn : 0 ≤ x) (hx_lt : x < 1 / 10 ^ p)
    (hval : φ = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)
    (hxbit : g.xbit_ = true ↔ 0 < x)
    (hall : allNibblesAtMost9 g.digits_)
    (hdvd : (10 : ℕ) ^ 16 ∣ decimalValue g.digits_ * 10 ^ p)
    (hsize : m.toNat * 10 ^ p < 10 ^ 23)
    (hcouple : x * 10 ^ 20 ≤ (m.toNat : ℚ) * 10 ^ p)
    (out : UInt64 × Int × Guard)
    (hok : doNormalize_capAtMaxRep m e g = .ok out) :
    ∃ (φ' x' : ℚ) (p' : ℕ),
      0 ≤ x' ∧ x' < 1 / 10 ^ p' ∧
      φ' = (decimalValue out.2.2.digits_ : ℚ) / 10 ^ 16 + x' ∧
      (out.2.2.xbit_ = true ↔ 0 < x') ∧
      allNibblesAtMost9 out.2.2.digits_ ∧
      (10 : ℕ) ^ 16 ∣ decimalValue out.2.2.digits_ * 10 ^ p' ∧
      out.1.toNat * 10 ^ p' < 10 ^ 23 ∧
      x' * 10 ^ 20 ≤ (out.1.toNat : ℚ) * 10 ^ p' ∧
      ((m.toNat : ℚ) + φ) * 10 ^ e = ((out.1.toNat : ℚ) + φ') * 10 ^ out.2.1 := by
  unfold doNormalize_capAtMaxRep at hok
  by_cases h_gt : m > maxRepUp
  · rw [if_pos h_gt] at hok
    by_cases h_ge : e ≥ maxExponent
    · rw [if_pos h_ge] at hok
      exact absurd hok (by intro h; cases h)
    · rw [if_neg h_ge] at hok
      unfold divu10 at hok
      simp only [] at hok
      obtain rfl := (Except.ok.inj hok).symm
      have h_gt_nat : maxRepUp.toNat < m.toNat := UInt64.lt_iff_toNat_lt.mp h_gt
      have hmaxRU : maxRepUp.toNat = 9223372036854775810 := by decide
      rw [hmaxRU] at h_gt_nat
      have h10 : (10 : UInt64).toNat = 10 := uint64_ten_toNat
      have h_div : (m / 10).toNat = m.toNat / 10 := by rw [UInt64.toNat_div, h10]
      have h_mod : (m % 10).toNat = m.toNat % 10 := by rw [UInt64.toNat_mod, h10]
      have h_d_lt : (m % 10).toNat < 10 := by rw [h_mod]; exact Nat.mod_lt _ (by norm_num)
      have hm_ge : (10 : ℕ) ^ 18 ≤ m.toNat := by omega
      have hp_le : p ≤ 4 := by
        by_contra hpc
        push_neg at hpc
        have h1 : (10 : ℕ) ^ 18 * 10 ^ p < 10 ^ 23 := lt_of_le_of_lt (Nat.mul_le_mul_right _ hm_ge) hsize
        have h2 : (10 : ℕ) ^ 23 ≤ 10 ^ 18 * 10 ^ p := by
          rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hdvd10 : 10 ∣ decimalValue g.digits_ := by
        have hsplit : (10 : ℕ) ^ 16 = 10 ^ (16 - p) * 10 ^ p := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit] at hdvd
        have hstep : (10 : ℕ) ^ (16 - p) ∣ decimalValue g.digits_ :=
          (Nat.mul_dvd_mul_iff_right (by positivity)).mp hdvd
        exact (dvd_pow_self 10 (show 16 - p ≠ 0 by omega)).trans hstep
      have hnib0 : nibble g.digits_ 0 = 0 := nibble_zero_of_ten_dvd g.digits_ hall hdvd10
      have hx'_nn : (0 : ℚ) ≤ x / 10 := by positivity
      have hx'_lt : x / 10 < 1 / 10 ^ (p + 1) := by
        have hp : (0 : ℚ) < 10 ^ p := by positivity
        have hxp : x * 10 ^ p < 1 := (lt_div_iff₀ hp).mp hx_lt
        rw [pow_succ, div_lt_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hxp, hp]
      have hval' : (φ + ((m % 10).toNat : ℚ)) / 10
          = (decimalValue (g.push (m % 10)).digits_ : ℚ) / 10 ^ 16 + x / 10 := by
        have hf := represents_push_formula (m % 10) h_d_lt φ hval
        rw [hf, hnib0]; push_cast; ring
      have hxbit' : (g.push (m % 10)).xbit_ = true ↔ 0 < x / 10 := by
        have h := represents_push_xbit (m % 10) hx_nn hxbit
        rw [hnib0] at h; simpa using h
      have hall' : allNibblesAtMost9 (g.push (m % 10)).digits_ :=
        allNibblesAtMost9_push g _ h_d_lt hall
      have hdvd' : (10 : ℕ) ^ 16 ∣ decimalValue (g.push (m % 10)).digits_ * 10 ^ (p + 1) := by
        have hpr := decimalValue_push g (m % 10)
        rw [hnib0, Nat.add_zero] at hpr
        have hd_eq : (m % 10).toNat % 16 = (m % 10).toNat := Nat.mod_eq_of_lt (by omega)
        rw [hd_eq] at hpr
        have key : decimalValue (g.push (m % 10)).digits_ * 10 ^ (p + 1)
            = decimalValue g.digits_ * 10 ^ p + (m % 10).toNat * 10 ^ 16 * 10 ^ p := by
          rw [pow_succ]
          calc decimalValue (g.push (m % 10)).digits_ * (10 ^ p * 10)
              = 10 * decimalValue (g.push (m % 10)).digits_ * 10 ^ p := by ring
            _ = (decimalValue g.digits_ + (m % 10).toNat * 10 ^ 16) * 10 ^ p := by rw [hpr]
            _ = decimalValue g.digits_ * 10 ^ p + (m % 10).toNat * 10 ^ 16 * 10 ^ p := by ring
        rw [key]
        exact Nat.dvd_add hdvd (by rw [show (m % 10).toNat * 10 ^ 16 * 10 ^ p
          = 10 ^ 16 * ((m % 10).toNat * 10 ^ p) from by ring]; exact Dvd.intro _ rfl)
      have hsize' : (m / 10).toNat * 10 ^ (p + 1) < 10 ^ 23 := by
        rw [h_div, pow_succ]
        calc m.toNat / 10 * (10 ^ p * 10) = (m.toNat / 10 * 10) * 10 ^ p := by ring
          _ ≤ m.toNat * 10 ^ p := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
          _ < 10 ^ 23 := hsize
      have hcouple' : (x / 10) * 10 ^ 20 ≤ ((m / 10).toNat : ℚ) * 10 ^ (p + 1) := by
        have hP : (0 : ℚ) < 10 ^ p := by positivity
        have hkey : (m.toNat : ℚ) ≤ ((m.toNat / 10 : ℕ) : ℚ) * 100 := by
          exact_mod_cast (show m.toNat ≤ m.toNat / 10 * 100 by omega)
        rw [h_div, show (x / 10) * 10 ^ 20 = (x * 10 ^ 20) / 10 from by ring,
            div_le_iff₀ (by norm_num : (0:ℚ) < 10), pow_succ 10 p]
        calc x * 10 ^ 20 ≤ (m.toNat : ℚ) * 10 ^ p := hcouple
          _ ≤ ((m.toNat / 10 : ℕ) : ℚ) * 100 * 10 ^ p := mul_le_mul_of_nonneg_right hkey hP.le
          _ = ((m.toNat / 10 : ℕ) : ℚ) * (10 ^ p * 10) * 10 := by ring
      refine ⟨(φ + ((m % 10).toNat : ℚ)) / 10, x / 10, p + 1,
        hx'_nn, hx'_lt, hval', hxbit', hall', hdvd', hsize', hcouple', ?_⟩
      have h_decomp : (m.toNat : ℚ) = ((m / 10).toNat : ℚ) * 10 + ((m % 10).toNat : ℚ) := by
        rw [h_div, h_mod]
        have h_nat : m.toNat = m.toNat / 10 * 10 + m.toNat % 10 := by omega
        have h_q : (m.toNat : ℚ) = ((m.toNat / 10 * 10 + m.toNat % 10 : ℕ) : ℚ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) h_nat
        rw [h_q]; push_cast; ring
      rw [h_decomp, show (10 : ℚ) ^ (e + 1) = 10 ^ e * 10 from by
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp]
      field_simp
      ring
  · rw [if_neg h_gt] at hok
    obtain rfl := (Except.ok.inj hok).symm
    exact ⟨φ, x, p, hx_nn, hx_lt, hval, hxbit, hall, hdvd, hsize, hcouple, by ring⟩

/-! ## Round-decision agreement -/

/-- **Case-B core.** When the captured digits sit strictly below the tie
(`decimalValue < 5·10^15`), the true fraction is strictly below `1/2`. The captured
digits occupy the top `p` nibbles (`10^16 ∣ decimalValue·10^p`), so their value is
at most `5·10^15 - 10^(16-p)`, which the tail `x < 1/10^p` cannot lift over the
midpoint. The `p = 0` corner (no digits captured) is supplied externally. -/
lemma valueInv_le_half_of_dec_lt (decVal : ℕ) (x f : ℚ) (p : ℕ)
    (_hx_nn : 0 ≤ x) (hx_lt : x < 1 / 10 ^ p)
    (hval : f = (decVal : ℚ) / 10 ^ 16 + x)
    (hdvd : (10 : ℕ) ^ 16 ∣ decVal * 10 ^ p)
    (hdlt : decVal < 5 * 10 ^ 15)
    (hp0 : p = 0 → f < 1 / 2) : f < 1 / 2 := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · exact hp0 hp
  by_cases hp16 : p ≤ 15
  · -- divisibility gives a 10^(16-p) gap below the tie
    have hdvd16p : (10 : ℕ) ^ (16 - p) ∣ decVal := by
      have hsplit : (10 : ℕ) ^ 16 = 10 ^ (16 - p) * 10 ^ p := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit] at hdvd
      exact (Nat.mul_dvd_mul_iff_right (by positivity)).mp hdvd
    have htie_dvd : (10 : ℕ) ^ (16 - p) ∣ 5 * 10 ^ 15 := by
      refine ⟨5 * 10 ^ (p - 1), ?_⟩
      rw [← mul_assoc, mul_comm ((10 : ℕ) ^ (16 - p)) 5, mul_assoc, ← pow_add]
      congr 2; omega
    -- decVal + 10^(16-p) ≤ 5·10^15 (a full step below the tie)
    have hle_nat : decVal + 10 ^ (16 - p) ≤ 5 * 10 ^ 15 := by
      obtain ⟨a, ha⟩ := hdvd16p
      obtain ⟨b, hb⟩ := htie_dvd
      have hab : a < b := by
        by_contra h; push_neg at h
        have : 5 * 10 ^ 15 ≤ decVal := by
          rw [ha, hb]; exact Nat.mul_le_mul (le_refl _) h
        omega
      calc decVal + 10 ^ (16 - p) = 10 ^ (16 - p) * (a + 1) := by rw [ha]; ring
        _ ≤ 10 ^ (16 - p) * b := Nat.mul_le_mul (le_refl _) (by omega)
        _ = 5 * 10 ^ 15 := hb.symm
    have hpowpos : (0 : ℚ) < 10 ^ (16 - p) := by positivity
    have hpowid2 : (10 : ℚ) ^ p * 10 ^ (16 - p) = 10 ^ 16 := by
      rw [← pow_add]; congr 1; omega
    have hxbound : x * 10 ^ p < 1 := (lt_div_iff₀ (by positivity)).mp hx_lt
    have hdle : (decVal : ℚ) + 10 ^ (16 - p) ≤ 5 * 10 ^ 15 := by exact_mod_cast hle_nat
    -- from x·10^p < 1: x·10^16 = x·10^p·10^(16-p) < 10^(16-p)
    have hx16 : x * 10 ^ 16 < 10 ^ (16 - p) := by
      have heq : x * 10 ^ 16 = (x * 10 ^ p) * 10 ^ (16 - p) := by
        rw [mul_assoc, hpowid2]
      rw [heq]; nlinarith [hxbound, hpowpos]
    rw [hval]
    have h16 : (0 : ℚ) < 10 ^ 16 := by positivity
    rw [div_add' _ _ _ (ne_of_gt h16), div_lt_div_iff₀ h16 (by norm_num)]
    nlinarith [hdle, hx16]
  · -- p ≥ 16: tail below 10^-16, integer gap of 1 suffices
    push_neg at hp16
    have hxbound : x < 1 / 10 ^ 16 := by
      have hle : (1 : ℚ) / 10 ^ p ≤ 1 / 10 ^ 16 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [hx_lt, hle]
    have hdle : (decVal : ℚ) + 1 ≤ 5 * 10 ^ 15 := by
      exact_mod_cast (show decVal + 1 ≤ 5 * 10 ^ 15 by omega)
    rw [hval]
    have h16 : (0 : ℚ) < 10 ^ 16 := by positivity
    rw [div_add' _ _ _ (ne_of_gt h16), div_lt_div_iff₀ h16 (by norm_num)]
    nlinarith [hdle, hxbound, h16]

/-- The midpoint decomposition of the value fraction against the captured digits. -/
private lemma valueInv_key (g : Guard) (f x : ℚ)
    (hval : f = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x) :
    f - 1 / 2 = ((decimalValue g.digits_ : ℚ) - 5 * 10 ^ 15) / 10 ^ 16 + x := by
  rw [hval]; field_simp; ring

/-- **Div round = 1 ⟹ f > ½.** The `to_nearest` guard rounds up only strictly above
the midpoint. Mirrors `represents_round_eq_one`, but for the true value fraction. -/
lemma div_round_eq_one (g : Guard) (f x : ℚ)
    (hx_nn : 0 ≤ x) (hval : f = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)
    (hxbit : g.xbit_ = true ↔ 0 < x) (hall : allNibblesAtMost9 g.digits_)
    (h1 : g.round .to_nearest = 1) : f > 1 / 2 := by
  have hne : ¬ g.empty := by
    intro he; unfold Guard.round at h1; rw [if_pos he] at h1; exact absurd h1 (by decide)
  rw [round_to_nearest_def hne] at h1
  have key := valueInv_key g f x hval
  have h16 : (0 : ℚ) < 10 ^ 16 := by positivity
  by_cases hgt : g.digits_ > 0x5000_0000_0000_0000
  · have hdec := (hex_gt_iff_dec_gt g.digits_ hall).mp hgt
    have hq : (decimalValue g.digits_ : ℚ) > 5 * 10 ^ 15 := by exact_mod_cast hdec
    have hpos : ((decimalValue g.digits_ : ℚ) - 5 * 10 ^ 15) / 10 ^ 16 > 0 :=
      div_pos (by linarith) h16
    linarith [key, hx_nn]
  · rw [if_neg hgt] at h1
    by_cases hlt : g.digits_ < 0x5000_0000_0000_0000
    · rw [if_pos hlt] at h1; exact absurd h1 (by decide)
    · rw [if_neg hlt] at h1
      have hdec : decimalValue g.digits_ = 5 * 10 ^ 15 :=
        (hex_eq_iff_dec_eq g.digits_ hall).mp ⟨hgt, hlt⟩
      have hq : ((decimalValue g.digits_ : ℚ) - 5 * 10 ^ 15) / 10 ^ 16 = 0 := by
        have : (decimalValue g.digits_ : ℚ) = 5 * 10 ^ 15 := by exact_mod_cast hdec
        rw [this]; ring
      by_cases hxb : g.xbit_ = true
      · have hxp : 0 < x := hxbit.mp hxb
        linarith only [key, hq, hxp]
      · rw [if_neg hxb] at h1
        exact absurd h1 (by decide)

/-- **Div round = 0 ⟹ f = ½.** Mirrors `represents_round_eq_zero`. -/
lemma div_round_eq_zero (g : Guard) (f x : ℚ)
    (hx_nn : 0 ≤ x) (hval : f = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)
    (hxbit : g.xbit_ = true ↔ 0 < x) (hall : allNibblesAtMost9 g.digits_)
    (h0 : g.round .to_nearest = 0) : f = 1 / 2 := by
  have hne : ¬ g.empty := by
    intro he; unfold Guard.round at h0; rw [if_pos he] at h0; exact absurd h0 (by decide)
  rw [round_to_nearest_def hne] at h0
  have key := valueInv_key g f x hval
  by_cases hgt : g.digits_ > 0x5000_0000_0000_0000
  · rw [if_pos hgt] at h0; exact absurd h0 (by decide)
  · rw [if_neg hgt] at h0
    by_cases hlt : g.digits_ < 0x5000_0000_0000_0000
    · rw [if_pos hlt] at h0; exact absurd h0 (by decide)
    · rw [if_neg hlt] at h0
      have hdec : decimalValue g.digits_ = 5 * 10 ^ 15 :=
        (hex_eq_iff_dec_eq g.digits_ hall).mp ⟨hgt, hlt⟩
      have hq : ((decimalValue g.digits_ : ℚ) - 5 * 10 ^ 15) / 10 ^ 16 = 0 := by
        have : (decimalValue g.digits_ : ℚ) = 5 * 10 ^ 15 := by exact_mod_cast hdec
        rw [this]; ring
      by_cases hxb : g.xbit_ = true
      · rw [if_pos hxb] at h0; exact absurd h0 (by decide)
      · have hx0 : x = 0 := by
          by_contra hxne
          exact absurd (hxbit.mpr (lt_of_le_of_ne hx_nn (Ne.symm hxne))) hxb
        rw [hx0] at key; linarith only [key, hq]

/-- **Div f > ½ ⟹ round = 1.** The hard direction: below the tie the captured
digits leave a `10^(16-p)` gap the tail cannot cross (`valueInv_le_half_of_dec_lt`),
so `f > ½` forces the guard above the tie. Mirrors `represents_f_gt_half`. -/
lemma div_f_gt_half (g : Guard) (f x : ℚ) (p : ℕ)
    (hx_nn : 0 ≤ x) (hx_lt : x < 1 / 10 ^ p)
    (hval : f = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)
    (hxbit : g.xbit_ = true ↔ 0 < x) (hall : allNibblesAtMost9 g.digits_)
    (hdvd : (10 : ℕ) ^ 16 ∣ decimalValue g.digits_ * 10 ^ p)
    (hp0 : p = 0 → f < 1 / 2)
    (h : f > 1 / 2) : g.round .to_nearest = 1 := by
  have key := valueInv_key g f x hval
  by_cases hgt : g.digits_ > 0x5000_0000_0000_0000
  · have hne : ¬ g.empty := by
      unfold Guard.empty Guard.unrecoverable
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true, not_and]
      intro hz; exact absurd (hz ▸ hgt) (by decide)
    rw [round_to_nearest_def hne, if_pos hgt]
  · by_cases hlt : g.digits_ < 0x5000_0000_0000_0000
    · -- below the tie: f ≤ 1/2, contradiction
      exfalso
      have hdec : decimalValue g.digits_ < 5 * 10 ^ 15 :=
        (hex_lt_iff_dec_lt g.digits_ hall).mp hlt
      have hle := valueInv_le_half_of_dec_lt (decimalValue g.digits_) x f p hx_nn hx_lt hval hdvd hdec hp0
      linarith only [hle, h]
    · -- at the tie: digits = 5·10^15, so f = 1/2 + x, and f > 1/2 forces xbit
      have hdec : decimalValue g.digits_ = 5 * 10 ^ 15 :=
        (hex_eq_iff_dec_eq g.digits_ hall).mp ⟨hgt, hlt⟩
      have hq : ((decimalValue g.digits_ : ℚ) - 5 * 10 ^ 15) / 10 ^ 16 = 0 := by
        have : (decimalValue g.digits_ : ℚ) = 5 * 10 ^ 15 := by exact_mod_cast hdec
        rw [this]; ring
      have hxp : 0 < x := by rw [hq] at key; linarith only [key, h]
      have hxb : g.xbit_ = true := hxbit.mpr hxp
      have hne : ¬ g.empty := by
        unfold Guard.empty Guard.unrecoverable; rw [hxb]; simp
      rw [round_to_nearest_def hne, if_neg hgt, if_neg hlt, if_pos hxb]

/-- **Div f = ½ ⟹ round = 0.** At an exact tie the captured digits are exactly the
half-mark and the tail vanishes (`¬xbit`). Mirrors the `f = ½ ↔ round = 0` clause of
`round_correct`. -/
lemma div_f_eq_half (g : Guard) (f x : ℚ) (p : ℕ)
    (hx_nn : 0 ≤ x) (hx_lt : x < 1 / 10 ^ p)
    (hval : f = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)
    (hxbit : g.xbit_ = true ↔ 0 < x) (hall : allNibblesAtMost9 g.digits_)
    (hdvd : (10 : ℕ) ^ 16 ∣ decimalValue g.digits_ * 10 ^ p)
    (hp0 : p = 0 → f < 1 / 2)
    (h : f = 1 / 2) : g.round .to_nearest = 0 := by
  have key := valueInv_key g f x hval
  by_cases hgt : g.digits_ > 0x5000_0000_0000_0000
  · -- digits > tie ⟹ f > ½, contradicting f = ½
    exfalso
    have hdec := (hex_gt_iff_dec_gt g.digits_ hall).mp hgt
    have hq : (decimalValue g.digits_ : ℚ) > 5 * 10 ^ 15 := by exact_mod_cast hdec
    have h16 : (0 : ℚ) < 10 ^ 16 := by positivity
    have hpos : ((decimalValue g.digits_ : ℚ) - 5 * 10 ^ 15) / 10 ^ 16 > 0 :=
      div_pos (by linarith) h16
    have hf2 : f > 1 / 2 := by linarith only [key, hx_nn, hpos]
    linarith only [hf2, h]
  · by_cases hlt : g.digits_ < 0x5000_0000_0000_0000
    · -- digits < tie ⟹ f < ½ (strict), contradicting f = ½
      exfalso
      have hdec : decimalValue g.digits_ < 5 * 10 ^ 15 :=
        (hex_lt_iff_dec_lt g.digits_ hall).mp hlt
      have hle := valueInv_le_half_of_dec_lt (decimalValue g.digits_) x f p hx_nn hx_lt hval hdvd hdec hp0
      linarith only [hle, h]
    · -- at the tie: x = 0, so ¬xbit, round = 0
      have hdec : decimalValue g.digits_ = 5 * 10 ^ 15 :=
        (hex_eq_iff_dec_eq g.digits_ hall).mp ⟨hgt, hlt⟩
      have hq : ((decimalValue g.digits_ : ℚ) - 5 * 10 ^ 15) / 10 ^ 16 = 0 := by
        have : (decimalValue g.digits_ : ℚ) = 5 * 10 ^ 15 := by exact_mod_cast hdec
        rw [this]; ring
      have hx0 : x = 0 := by rw [hq] at key; linarith only [key, h, hx_nn]
      have hxb : g.xbit_ ≠ true := by
        intro hxb; exact absurd (hxbit.mp hxb) (by rw [hx0]; exact lt_irrefl 0)
      have hne : ¬ g.empty := by
        intro he
        -- empty ⟹ f = 0, contradicting f = 1/2
        have hdz : g.digits_ = 0 := by
          have h' : (g.digits_ == 0 && !g.xbit_) = true := he
          rw [Bool.and_eq_true, beq_iff_eq] at h'; exact h'.1
        have : decimalValue g.digits_ = 0 := by rw [hdz, decimalValue_zero]
        rw [this] at hdec; norm_num at hdec
      rw [round_to_nearest_def hne, if_neg hgt, if_neg hlt, if_neg hxb]

/-- `decimalValue` of a valid decimal guard fits in 16 digits. -/
lemma decimalValue_lt_pow16 (d : UInt64) (hall : allNibblesAtMost9 d) :
    decimalValue d < 10 ^ 16 := by
  obtain ⟨heq, hlt⟩ := decimalValue_decomp d hall
  have h15 : nibble d 15 ≤ 9 := hall ⟨15, by omega⟩
  rw [heq]
  have : nibble d 15 * 10 ^ 15 ≤ 9 * 10 ^ 15 := Nat.mul_le_mul_right _ h15
  have h15pow : (10 : ℕ) ^ 15 < 10 ^ 16 := by norm_num
  omega

/-- **`p = 0` corner discharge.** When no digit was captured (`p = 0`), the guard
holds no digits (`decimalValue = 0`), so `f = x`, and the coupling
`x·10^20 ≤ zm` with `zm < 10^19` forces `x < 1/10 ≤ 1/2`. This supplies the
external `hp0` hypothesis of `div_f_gt_half` for the div pipeline (no scale-down or
cap push happened, so the output mantissa `zm ≤ maxRepUp < 10^19`). -/
lemma valueInv_p0_le_half (g : Guard) (f x : ℚ) (zm : ℕ)
    (hval : f = (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)
    (hall : allNibblesAtMost9 g.digits_)
    (hdvd : (10 : ℕ) ^ 16 ∣ decimalValue g.digits_ * 10 ^ 0)
    (hcouple : x * 10 ^ 20 ≤ (zm : ℚ) * 10 ^ 0)
    (hzm : zm < 10 ^ 19) : f < 1 / 2 := by
  simp only [pow_zero, mul_one] at hdvd hcouple
  have hdv0 : decimalValue g.digits_ = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd (decimalValue_lt_pow16 g.digits_ hall)
  rw [hval, hdv0, Nat.cast_zero, zero_div, zero_add]
  have hzmq : (zm : ℚ) < 10 ^ 19 := by exact_mod_cast hzm
  have h20 : (0 : ℚ) < 10 ^ 20 := by positivity
  rw [show (1 : ℚ) / 2 = (5 * 10 ^ 19) / 10 ^ 20 from by norm_num, lt_div_iff₀ h20]
  linarith [hcouple, hzmq]

end XRPL.Model.Protocol
