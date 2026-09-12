import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.GridPoint
import XRPL.Properties.Protocol.Number.Common.Closest.Normalize
import XRPL.Properties.Protocol.Number.Common.Closest.Existence

/-! # Cusp-aware round-to-representable monotonicity core

`Number.RoundsCuspAware r t` pins `r` as `t`'s grid image with just enough
directional information to prove monotonicity, INCLUDING the cusp exact-tie where
the model rounds to the far neighbour (so `NearestTo`/`RoundsNearestEven` fail):

* rounding down: `r = lower t` and `2t ≤ L+U` for the cell midpoint;
* rounding up: `r = upper t` and either `L+U ≤ 2t` (`t ≥` midpoint) OR the
  "cusp-tie escape" `2t(maxRep+1) > maxRep(L+U)` — the sole sub-midpoint round-up,
  which sits so close to `L` that the normalized minimal-relative-gap forbids any
  larger reachable product from landing back below the midpoint.

The direction clauses quantify over the *other* neighbour, so the predicate only
asserts existence of the neighbour `r` equals; the other is recovered for free in
the single cross case from `upper`/`lower` minimality.

`roundsCuspAware_mono` proves monotonicity from this plus the normalized gap bound
(as `t₁ ≤ maxRep(t₂−t₁)`) and rounding determinism at a tie. -/

namespace XRPL.Model.Protocol

/-! ## Grid-neighbour monotonicity helpers (re-derived from `Tightness`) -/

theorem Number.lowerV_mono (t₁ t₂ : ℚ) (n₁ n₂ : Number)
    (h₁ : Number.lower t₁ = some n₁) (h₂ : Number.lower t₂ = some n₂)
    (hle : t₁ ≤ t₂) : n₁.toRat ≤ n₂.toRat :=
  Number.lower_tight t₂ n₂ h₂ n₁ (Number.lower_isNormalized t₁ n₁ h₁)
    (le_trans (Number.lower_le t₁ n₁ h₁) hle)

theorem Number.upperV_mono (t₁ t₂ : ℚ) (n₁ n₂ : Number)
    (h₁ : Number.upper t₁ = some n₁) (h₂ : Number.upper t₂ = some n₂)
    (hle : t₁ ≤ t₂) : n₁.toRat ≤ n₂.toRat :=
  Number.upper_tight t₁ n₁ h₁ n₂ (Number.upper_isNormalized t₂ n₂ h₂)
    (le_trans hle (Number.upper_ge t₂ n₂ h₂))

theorem Number.no_gridV_between (t : ℚ) (L U : Number)
    (hL : Number.lower t = some L) (hU : Number.upper t = some U)
    (g : Number) (hg : g.isNormalized) :
    ¬ (L.toRat < g.toRat ∧ g.toRat < U.toRat) := by
  rintro ⟨h1, h2⟩
  by_cases hgt : g.toRat ≤ t
  · exact absurd (Number.lower_tight t L hL g hg hgt) (not_le.mpr h1)
  · push_neg at hgt
    exact absurd (Number.upper_tight t U hU g hg (le_of_lt hgt)) (not_le.mpr h2)

/-! ## The predicate -/

/-- `r` is `t`'s cusp-aware grid image. See the module doc. -/
def Number.RoundsCuspAware (r : Number) (t : ℚ) : Prop :=
  (∃ L, Number.lower t = some L ∧ r.toRat = L.toRat ∧
     (∀ U, Number.upper t = some U → 2 * t ≤ L.toRat + U.toRat))
  ∨
  (∃ U, Number.upper t = some U ∧ r.toRat = U.toRat ∧
     (∀ L, Number.lower t = some L →
       2 * t * ((maxRepNat : ℚ) + 1) > (maxRepNat : ℚ) * (L.toRat + U.toRat)))

/-! ## The monotonicity core -/

/-- **Cusp-aware round monotonicity.** If `t₁ ≤ t₂`, each `rᵢ` is `tᵢ`'s cusp-aware
grid image, the results are positive, `0 < t₁`, the normalized gap bound
`t₁ ≤ maxRep(t₂−t₁)` holds under `t₁ < t₂`, and rounding is deterministic at a tie,
then `r₁.toRat ≤ r₂.toRat`. -/
theorem roundsCuspAware_mono (t₁ t₂ : ℚ) (r₁ r₂ : Number)
    (h₁ : r₁.RoundsCuspAware t₁) (h₂ : r₂.RoundsCuspAware t₂)
    (hr₁pos : 0 < r₁.toRat) (hr₂pos : 0 < r₂.toRat) (ht₁pos : 0 < t₁)
    (hle : t₁ ≤ t₂)
    (hgap : t₁ < t₂ → t₁ ≤ (maxRepNat : ℚ) * (t₂ - t₁))
    (hdet : t₁ = t₂ → r₁.toRat = r₂.toRat) :
    r₁.toRat ≤ r₂.toRat := by
  have ht₂pos : 0 < t₂ := lt_of_lt_of_le ht₁pos hle
  rcases h₁ with ⟨L₁, hL₁, hr₁, hdn₁⟩ | ⟨U₁, hU₁, hr₁, hup₁⟩
  · rcases h₂ with ⟨L₂, hL₂, hr₂, hdn₂⟩ | ⟨U₂, hU₂, hr₂, hup₂⟩
    · rw [hr₁, hr₂]; exact Number.lowerV_mono t₁ t₂ L₁ L₂ hL₁ hL₂ hle
    · rw [hr₁, hr₂]
      calc L₁.toRat ≤ t₁ := Number.lower_le t₁ L₁ hL₁
        _ ≤ t₂ := hle
        _ ≤ U₂.toRat := Number.upper_ge t₂ U₂ hU₂
  · rcases h₂ with ⟨L₂, hL₂, hr₂, hdn₂⟩ | ⟨U₂, hU₂, hr₂, hup₂⟩
    · -- cross: r₁ = upper t₁, r₂ = lower t₂
      rw [hr₁, hr₂]
      by_contra hcon
      push_neg at hcon  -- hcon : L₂.toRat < U₁.toRat
      have hL₂pos : 0 < L₂.toRat := hr₂ ▸ hr₂pos
      have hU₁pos : 0 < U₁.toRat := hr₁ ▸ hr₁pos
      have hL₂norm : L₂.isNormalized := Number.lower_isNormalized t₂ L₂ hL₂
      have hU₁norm : U₁.isNormalized := Number.upper_isNormalized t₁ U₁ hU₁
      -- L₂ < t₁ (else `upper t₁` minimality is violated by L₂)
      have hL₂_lt_t₁ : L₂.toRat < t₁ := by
        by_contra h; push_neg at h
        exact absurd (Number.upper_tight t₁ U₁ hU₁ L₂ hL₂norm h) (not_le.mpr hcon)
      -- U₁ > t₂ (else `lower t₂` maximality is violated by U₁)
      have hU₁_gt_t₂ : t₂ < U₁.toRat := by
        by_contra h; push_neg at h
        exact absurd (Number.lower_tight t₂ L₂ hL₂ U₁ hU₁norm h) (not_le.mpr hcon)
      -- recover the missing neighbours
      obtain ⟨L₁, hL₁⟩ := Number.lower_some_of_pos_witnesses t₁ ht₁pos
        L₂ hL₂norm hL₂pos (le_of_lt hL₂_lt_t₁) U₁ hU₁norm (Number.upper_ge t₁ U₁ hU₁)
      obtain ⟨U₂, hU₂⟩ := Number.upper_some_of_pos_witnesses t₂ ht₂pos
        L₂ hL₂norm hL₂pos (Number.lower_le t₂ L₂ hL₂) U₁ hU₁norm (le_of_lt hU₁_gt_t₂)
      have hLL : L₁.toRat ≤ L₂.toRat := Number.lowerV_mono t₁ t₂ L₁ L₂ hL₁ hL₂ hle
      have hUU : U₁.toRat ≤ U₂.toRat := Number.upperV_mono t₁ t₂ U₁ U₂ hU₁ hU₂ hle
      have hU₁neL₁ : L₁.toRat ≠ U₁.toRat := fun heq => by
        have : L₂.toRat < L₁.toRat := by rw [heq]; exact hcon
        exact absurd hLL (not_le.mpr this)
      have hL₁eqL₂ : L₁.toRat = L₂.toRat := by
        rcases lt_or_eq_of_le hLL with hlt | heq
        · exact absurd ⟨hlt, hcon⟩
            (Number.no_gridV_between t₁ L₁ U₁ hL₁ hU₁ L₂ hL₂norm)
        · exact heq
      have hU₁eqU₂ : U₁.toRat = U₂.toRat := by
        rcases lt_or_eq_of_le hUU with hlt | heq
        · exact absurd ⟨hcon, hlt⟩
            (Number.no_gridV_between t₂ L₂ U₂ hL₂ hU₂ U₁ hU₁norm)
        · exact heq
      have hsum : L₁.toRat + U₁.toRat = L₂.toRat + U₂.toRat := by rw [hL₁eqL₂, hU₁eqU₂]
      have hd2 : 2 * t₂ ≤ L₂.toRat + U₂.toRat := hdn₂ U₂ hU₂
      have htie1 : 2 * t₁ * ((maxRepNat : ℚ) + 1) > (maxRepNat : ℚ) * (L₁.toRat + U₁.toRat) :=
        hup₁ L₁ hL₁
      rcases lt_or_eq_of_le hle with htlt | hteq
      · have hgap' : t₁ ≤ (maxRepNat : ℚ) * (t₂ - t₁) := hgap htlt
        have h2t2 : 2 * t₂ ≤ L₁.toRat + U₁.toRat := by rw [hsum]; exact hd2
        have hmr : (0 : ℚ) < (maxRepNat : ℚ) := by norm_num
        nlinarith [htie1, h2t2, hgap', hmr]
      · exact absurd (by rw [← hr₁, ← hr₂]; exact hdet hteq) (ne_of_gt hcon)
    · rw [hr₁, hr₂]; exact Number.upperV_mono t₁ t₂ U₁ U₂ hU₁ hU₂ hle

end XRPL.Model.Protocol
