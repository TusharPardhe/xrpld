import XRPL.Properties.Protocol.Number.RoundMonotoneCusp
import XRPL.Properties.Vault.Common.RoundMonotoneGap
import XRPL.Properties.Vault.Common.MonotoneCore

/-! # Vault cusp-aware rounding composition wrappers

This Vault layer consumes and re-exports the protocol-level
`Number.RoundsCuspAware` predicate and `roundsCuspAware_mono` core.  It retains
only the multiplication and division composition wrappers that depend on the
Vault normalized-gap and tie-determinism lemmas. -/

namespace XRPL.Model.Protocol

/-! ## Composition wrappers: `RoundsCuspAware` ⇒ one-operand monotonicity -/

/-- **`operator_mul` monotone in one factor at `.to_nearest`** for fixed positive
`x`, given both results are positive cusp-aware grid images. -/
theorem operator_mul_left_mono_of_cuspAware (x y₁ y₂ r₁ r₂ : Number)
    (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hok₁ : Number.operator_mul x y₁ .to_nearest = .ok r₁)
    (hok₂ : Number.operator_mul x y₂ .to_nearest = .ok r₂)
    (hn₁ : r₁.RoundsCuspAware (x.toRat * y₁.toRat))
    (hn₂ : r₂.RoundsCuspAware (x.toRat * y₂.toRat))
    (hr₁pos : 0 < r₁.toRat) (hr₂pos : 0 < r₂.toRat)
    (hx : 0 < x.toRat) (hy₁pos : 0 < y₁.toRat) (hle : y₁.toRat ≤ y₂.toRat) :
    r₁.toRat ≤ r₂.toRat := by
  refine roundsCuspAware_mono _ _ r₁ r₂ hn₁ hn₂ hr₁pos hr₂pos (by positivity)
    (mul_le_mul_of_nonneg_left hle (le_of_lt hx)) ?_ ?_
  · intro hlt
    have hy_lt : y₁.toRat < y₂.toRat := lt_of_mul_lt_mul_left hlt (le_of_lt hx)
    have hgap := normalized_gap_bound y₁ y₂ hy₁ hy₂ hy₁pos hy_lt
    calc x.toRat * y₁.toRat
        ≤ x.toRat * ((maxRepNat : ℚ) * (y₂.toRat - y₁.toRat)) :=
          mul_le_mul_of_nonneg_left hgap (le_of_lt hx)
      _ = (maxRepNat : ℚ) * (x.toRat * y₂.toRat - x.toRat * y₁.toRat) := by ring
  · intro heq
    exact operator_mul_toRat_eq_of_truth_eq x y₁ y₂ r₁ r₂ hy₁ hy₂ hok₁ hok₂ (ne_of_gt hx) heq

/-- **`operator_div` monotone in the numerator at `.to_nearest`** for fixed positive
divisor `b`, given both results are positive cusp-aware grid images. -/
theorem operator_div_num_mono_of_cuspAware (a₁ a₂ b r₁ r₂ : Number)
    (ha₁ : a₁.isNormalized) (ha₂ : a₂.isNormalized)
    (hok₁ : Number.operator_div a₁ b .to_nearest = .ok r₁)
    (hok₂ : Number.operator_div a₂ b .to_nearest = .ok r₂)
    (hn₁ : r₁.RoundsCuspAware (a₁.toRat / b.toRat))
    (hn₂ : r₂.RoundsCuspAware (a₂.toRat / b.toRat))
    (hr₁pos : 0 < r₁.toRat) (hr₂pos : 0 < r₂.toRat)
    (hb : 0 < b.toRat) (ha₁pos : 0 < a₁.toRat) (hle : a₁.toRat ≤ a₂.toRat) :
    r₁.toRat ≤ r₂.toRat := by
  refine roundsCuspAware_mono _ _ r₁ r₂ hn₁ hn₂ hr₁pos hr₂pos (by positivity)
    (by gcongr) ?_ ?_
  · intro hlt
    have ha_lt : a₁.toRat < a₂.toRat := by
      by_contra h; push_neg at h
      have : a₂.toRat / b.toRat ≤ a₁.toRat / b.toRat := by gcongr
      exact absurd this (not_le.mpr hlt)
    have hgap := normalized_gap_bound a₁ a₂ ha₁ ha₂ ha₁pos ha_lt
    have hbne : b.toRat ≠ 0 := ne_of_gt hb
    calc a₁.toRat / b.toRat
        ≤ ((maxRepNat : ℚ) * (a₂.toRat - a₁.toRat)) / b.toRat := by gcongr
      _ = (maxRepNat : ℚ) * (a₂.toRat / b.toRat - a₁.toRat / b.toRat) := by
          field_simp
  · intro heq
    exact operator_div_toRat_eq_of_truth_eq a₁ a₂ b r₁ r₂ ha₁ ha₂ hok₁ hok₂ (ne_of_gt hb) heq

end XRPL.Model.Protocol
