import XRPL.Properties.Protocol.Number.Common.Defs
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.GridPoint
import XRPL.Properties.Vault.Common.DepositAccuracy

/-! # Algorithmic determinism / monotonicity for the `Number` rounding pipeline

The vault's `deposit_shares_monotone` and `withdraw_raw_payout_monotone` claims are
*rounding monotonicity*: a larger exact input buys at least as many shares / has
at least as large a raw priced payout. Final withdrawal-debit order additionally
uses the source-path post-sum clamp classification. This is not a consequence of `RoundsToRepresentable` alone -- the
two-neighbour disjunction does not pin the nearest choice at a tie. The `Number`
model functions are deterministic (one `.ok` result via a fixed tie-break), and a
consistent tie-break is monotone.

This file builds that monotonicity as a reusable layer at the `Number`/`STAmount`
level. No vault theorems live here.

## Layer 1: grid monotonicity

`Number.lower`/`Number.upper` are the deterministic grid-neighbour functions. They
are monotone because `Number.lower q` is *the largest* representable `≤ q` and
`Number.upper q` is *the smallest* representable `≥ q` (`Number.lower_tight` /
`Number.upper_tight`).
-/

namespace XRPL.Model.Protocol

/-- `Number.lower` is monotone in its argument (values). Immediate from
`Number.lower_tight`: `lower t₂` is the largest representable `≤ t₂`, and
`lower t₁ ≤ t₁ ≤ t₂` is a representable candidate. -/
theorem Number.lower_toRat_mono (t₁ t₂ : ℚ) (n₁ n₂ : Number)
    (h₁ : Number.lower t₁ = some n₁) (h₂ : Number.lower t₂ = some n₂)
    (hle : t₁ ≤ t₂) : n₁.toRat ≤ n₂.toRat :=
  Number.lower_tight t₂ n₂ h₂ n₁ (Number.lower_isNormalized t₁ n₁ h₁)
    (le_trans (Number.lower_le t₁ n₁ h₁) hle)

/-- `Number.upper` is monotone in its argument (values). Immediate from
`Number.upper_tight`: `upper t₁` is the smallest representable `≥ t₁`, and
`upper t₂ ≥ t₂ ≥ t₁` is a representable candidate. -/
theorem Number.upper_toRat_mono (t₁ t₂ : ℚ) (n₁ n₂ : Number)
    (h₁ : Number.upper t₁ = some n₁) (h₂ : Number.upper t₂ = some n₂)
    (hle : t₁ ≤ t₂) : n₁.toRat ≤ n₂.toRat :=
  Number.upper_tight t₁ n₁ h₁ n₂ (Number.upper_isNormalized t₂ n₂ h₂)
    (le_trans hle (Number.upper_ge t₂ n₂ h₂))

/-- `Number.lower t ≤ Number.upper t` (values): both sandwich `t`. -/
theorem Number.lower_le_upper (t : ℚ) (L U : Number)
    (hL : Number.lower t = some L) (hU : Number.upper t = some U) :
    L.toRat ≤ U.toRat :=
  le_trans (Number.lower_le t L hL) (Number.upper_ge t U hU)

/-- The two grid neighbours of `t` are adjacent: no normalized `Number` sits
strictly between `Number.lower t` and `Number.upper t`. -/
theorem Number.no_grid_strictly_between (t : ℚ) (L U : Number)
    (hL : Number.lower t = some L) (hU : Number.upper t = some U)
    (g : Number) (hg : g.isNormalized) :
    ¬ (L.toRat < g.toRat ∧ g.toRat < U.toRat) := by
  rintro ⟨h1, h2⟩
  by_cases hgt : g.toRat ≤ t
  · exact absurd (Number.lower_tight t L hL g hg hgt) (not_le.mpr h1)
  · push_neg at hgt
    exact absurd (Number.upper_tight t U hU g hg (le_of_lt hgt)) (not_le.mpr h2)

/-! ## Layer 2: round-to-nearest-even, characterized and monotone

`RoundsNearestEven r t` pins `r` as the correctly rounded (nearest, ties to even)
image of the exact value `t` onto the representable grid. Unlike
`RoundsToRepresentable`, the direction and tie clauses make `r.toRat` a *function*
of `t`, which is what monotonicity needs. -/

/-- `r` is the round-to-nearest-ties-to-even image of `t`: it is one of the two
grid neighbours `L = lower t`, `U = upper t`; it is the lower one when `t` is
strictly below the midpoint, the upper one when strictly above, and at an exact
midpoint the tie is broken toward the neighbour with an even *logical grid index*
`⌊L.toRat / (U.toRat - L.toRat)⌋`.

The tie parity is read off the logical grid index, not the stored
`L.mantissa_`. In the sub-`10^18` cusp band the model stores the mantissa of a
grid point as `10 · zm` (always even), so `L.mantissa_` loses the `zm` the model
actually breaks ties on. The floor `⌊L / (U - L)⌋` recovers `zm` in every band:
the grid step is `U - L`, and `L` is `zm` steps from zero, so the quotient is the
integer `zm`. In the normal decade this equals `L.mantissa_`, matching the naive
reading; in the cusp it recovers the true index. This is exactly the
`mantissa % 2 == 1` tie rule of `Guard.doRoundUp` (round the scaled mantissa `zm`
half-to-even). -/
def Number.RoundsNearestEven (r : Number) (t : ℚ) : Prop :=
  ∃ L U : Number,
    Number.lower t = some L ∧ Number.upper t = some U ∧
    (r.toRat = L.toRat ∨ r.toRat = U.toRat) ∧
    (2 * t < L.toRat + U.toRat → r.toRat = L.toRat) ∧
    (L.toRat + U.toRat < 2 * t → r.toRat = U.toRat) ∧
    (2 * t = L.toRat + U.toRat →
      (Even ⌊L.toRat / (U.toRat - L.toRat)⌋ → r.toRat = L.toRat) ∧
      (¬ Even ⌊L.toRat / (U.toRat - L.toRat)⌋ → r.toRat = U.toRat))

/-- **Round-to-nearest-even is monotone.** If `t₁ ≤ t₂` and each `rᵢ` is the
nearest-even image of `tᵢ`, then `r₁.toRat ≤ r₂.toRat`.

The proof reduces every configuration to `Number.lower`/`Number.upper`
monotonicity, except the single "cross" configuration `r₁ = upper t₁`,
`r₂ = lower t₂`. There, adjacency forces the two cells to coincide and the
midpoint clauses force `t₁ = t₂` exactly, so `lower`/`upper` agree as `Number`s
and the shared tie-break makes `r₁ = r₂` -- contradicting the cross. -/
theorem Number.roundsNearestEven_mono (t₁ t₂ : ℚ) (r₁ r₂ : Number)
    (h₁ : r₁.RoundsNearestEven t₁) (h₂ : r₂.RoundsNearestEven t₂)
    (hle : t₁ ≤ t₂) : r₁.toRat ≤ r₂.toRat := by
  obtain ⟨L₁, U₁, hL₁, hU₁, hmem₁, hdn₁, hup₁, htie₁⟩ := h₁
  obtain ⟨L₂, U₂, hL₂, hU₂, hmem₂, hdn₂, hup₂, htie₂⟩ := h₂
  -- grid monotonicity between the two cells
  have hLL : L₁.toRat ≤ L₂.toRat := Number.lower_toRat_mono t₁ t₂ L₁ L₂ hL₁ hL₂ hle
  have hUU : U₁.toRat ≤ U₂.toRat := Number.upper_toRat_mono t₁ t₂ U₁ U₂ hU₁ hU₂ hle
  have hL₂U₂ : L₂.toRat ≤ U₂.toRat := Number.lower_le_upper t₂ L₂ U₂ hL₂ hU₂
  rcases hmem₁ with hr₁L | hr₁U
  · -- r₁ = lower t₁ ≤ lower t₂ ≤ r₂
    rcases hmem₂ with hr₂L | hr₂U
    · rw [hr₁L, hr₂L]; exact hLL
    · rw [hr₁L, hr₂U]; exact le_trans hLL hL₂U₂
  · rcases hmem₂ with hr₂L | hr₂U
    · -- the cross: r₁ = upper t₁, r₂ = lower t₂. Suppose r₁ > r₂ and derive ⊥.
      by_contra hcon
      push_neg at hcon
      rw [hr₁U, hr₂L] at hcon  -- hcon : L₂.toRat < U₁.toRat
      -- if U₁ collapses to L₁, we are in the handled `r₁ = lower` case
      have hU₁neL₁ : L₁.toRat ≠ U₁.toRat := by
        intro heq
        have : L₂.toRat < L₁.toRat := by rw [heq]; exact hcon
        exact absurd hLL (not_le.mpr this)
      -- L₁ = L₂ as values: else L₂ is a grid point strictly between L₁ and U₁
      have hL₁eqL₂ : L₁.toRat = L₂.toRat := by
        rcases lt_or_eq_of_le hLL with hlt | heq
        · exact absurd ⟨hlt, hcon⟩
            (Number.no_grid_strictly_between t₁ L₁ U₁ hL₁ hU₁ L₂
              (Number.lower_isNormalized t₂ L₂ hL₂))
        · exact heq
      -- U₁ = U₂ as values: else U₁ is a grid point strictly between L₂ and U₂
      have hU₁eqU₂ : U₁.toRat = U₂.toRat := by
        rcases lt_or_eq_of_le hUU with hlt | heq
        · refine absurd ⟨?_, hlt⟩
            (Number.no_grid_strictly_between t₂ L₂ U₂ hL₂ hU₂ U₁
              (Number.upper_isNormalized t₁ U₁ hU₁))
          exact hcon
        · exact heq
      -- direction clauses. r₁ = U₁ ≠ L₁ forces t₁ ≥ midpoint₁, and r₂ = L₂ ≠ U₂ forces t₂ ≤ midpoint₂
      have hL₂neU₂ : L₂.toRat ≠ U₂.toRat := by
        rw [← hU₁eqU₂, ← hL₁eqL₂]; exact hU₁neL₁
      have ht₁mid : L₁.toRat + U₁.toRat ≤ 2 * t₁ := by
        by_contra h
        push_neg at h
        exact hU₁neL₁ (by rw [← hr₁U, hdn₁ h])
      have ht₂mid : 2 * t₂ ≤ L₂.toRat + U₂.toRat := by
        by_contra h
        push_neg at h
        exact hL₂neU₂ (by rw [← hr₂L]; exact hup₂ h)
      -- t₁ = t₂ exactly, at the shared midpoint
      have hsum : L₁.toRat + U₁.toRat = L₂.toRat + U₂.toRat := by
        rw [hL₁eqL₂, hU₁eqU₂]
      have ht₁eq : 2 * t₁ = L₁.toRat + U₁.toRat := by
        linarith [ht₁mid, ht₂mid, hsum, hle]
      have ht₂eq : 2 * t₂ = L₂.toRat + U₂.toRat := by
        linarith [ht₁mid, ht₂mid, hsum, hle]
      -- the logical grid index is shared: `L`, `U` agree as values across the cross,
      -- so `⌊L/(U-L)⌋` -- a function of those two values -- is literally equal.
      have hidx : (⌊L₁.toRat / (U₁.toRat - L₁.toRat)⌋ : ℤ)
          = ⌊L₂.toRat / (U₂.toRat - L₂.toRat)⌋ := by
        rw [hL₁eqL₂, hU₁eqU₂]
      by_cases hev : Even ⌊L₁.toRat / (U₁.toRat - L₁.toRat)⌋
      · have h1 := (htie₁ ht₁eq).1 hev
        -- r₁ = U₁ but the tie clause says r₁ = L₁, with L₁ ≠ U₁
        rw [hr₁U] at h1
        exact hU₁neL₁ h1.symm
      · have hev₂ : ¬ Even ⌊L₂.toRat / (U₂.toRat - L₂.toRat)⌋ := by rw [← hidx]; exact hev
        have h2 := (htie₂ ht₂eq).2 hev₂
        rw [hr₂L] at h2
        exact hL₂neU₂ h2
    · -- r₁ = upper t₁ ≤ upper t₂ = r₂
      rw [hr₁U, hr₂U]; exact hUU

/-- **Connection core for the per-operation bridges.** Given the exact grid
neighbours of `t` as `L = zm·10^e` and `U = (zm+1)·10^e` (a *regular* grid cell,
step `10^e`), plus the model's round decision expressed through the fractional
position `f` (`t = (zm+f)·10^e`), assemble `result.RoundsNearestEven t`.

This isolates the algebra of `RoundsNearestEven`'s three clauses from the hard
part (identifying the neighbours and the decision). The midpoint of the cell is
`(zm+½)·10^e`, so `2t ⋛ L+U ⟺ f ⋛ ½`, and the logical index
`⌊L/(U-L)⌋ = ⌊zm·10^e / 10^e⌋ = zm`, matching the tie rule the model applies to
the scaled mantissa `zm`. A per-operation bridge supplies `hLval`/`hUval` (from
the decade/grid identification of `lower`/`upper`), `hmem` (from
`RoundsToRepresentable`), and `hdown`/`hup` (from `round_correct` on the guard,
`Guard.shouldRoundUp_to_nearest`, and the `doRoundUp` value characterisations,
across the sign split). -/
theorem Number.roundsNearestEven_of_clean_cell
    (t : ℚ) (zm : ℕ) (e : ℤ) (f : ℚ) (L U result : Number)
    (hval : t = ((zm : ℚ) + f) * 10 ^ e)
    (hL : Number.lower t = some L) (hU : Number.upper t = some U)
    (hLval : L.toRat = (zm : ℚ) * 10 ^ e)
    (hUval : U.toRat = ((zm : ℚ) + 1) * 10 ^ e)
    (hmem : result.toRat = L.toRat ∨ result.toRat = U.toRat)
    (hdown : (f < 1 / 2 ∨ (f = 1 / 2 ∧ Even zm)) → result.toRat = L.toRat)
    (hup : (1 / 2 < f ∨ (f = 1 / 2 ∧ ¬ Even zm)) → result.toRat = U.toRat) :
    result.RoundsNearestEven t := by
  have hpow : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  refine ⟨L, U, hL, hU, hmem, ?_, ?_, ?_⟩
  · intro h
    rw [hval, hLval, hUval] at h
    exact hdown (Or.inl (by nlinarith [hpow]))
  · intro h
    rw [hval, hLval, hUval] at h
    exact hup (Or.inl (by nlinarith [hpow]))
  · intro h
    rw [hval, hLval, hUval] at h
    have hf : f = 1 / 2 := by nlinarith [hpow]
    have hidx : ⌊L.toRat / (U.toRat - L.toRat)⌋ = (zm : ℤ) := by
      rw [hLval, hUval, show ((zm : ℚ) + 1) * 10 ^ e - (zm : ℚ) * 10 ^ e = 10 ^ e from by ring,
          mul_div_assoc, div_self (ne_of_gt hpow), mul_one, Int.floor_natCast]
    refine ⟨fun hev => hdown (Or.inr ⟨hf, ?_⟩), fun hev => hup (Or.inr ⟨hf, ?_⟩)⟩
    · rw [hidx] at hev; exact_mod_cast hev
    · rw [hidx] at hev; exact fun hz => hev (by exact_mod_cast hz)

/-! ## Layer 3: `Number.truncate` monotone (toward zero, on nonnegative inputs)

`Number.truncate` floors a nonnegative normalized value (`Number.truncate_floor`),
and `⌊·⌋` is monotone. The vault applies `truncate` to nonnegative share counts. -/

/-- `Number.truncate` is monotone on nonnegative normalized inputs. -/
theorem Number.truncate_toRat_mono (n₁ n₂ t₁ t₂ : Number)
    (hn₁ : n₁.isNormalized) (hn₂ : n₂.isNormalized)
    (hneg₁ : n₁.negative_ = false) (hneg₂ : n₂.negative_ = false)
    (hok₁ : n₁.truncate = .ok t₁) (hok₂ : n₂.truncate = .ok t₂)
    (hle : n₁.toRat ≤ n₂.toRat) : t₁.toRat ≤ t₂.toRat := by
  rw [(Number.truncate_floor n₁ t₁ hn₁ hneg₁ hok₁).1,
      (Number.truncate_floor n₂ t₂ hn₂ hneg₂ hok₂).1]
  exact_mod_cast Int.floor_mono hle

/-! ## Layer 4: `STAmount.ofNumber` monotone on integer-valued inputs

For an integral `NumericType` and an integer-valued (`den = 1`) normalized
`Number`, `STAmount.ofNumber` is exact in any mode (`ofNumber_integral_exact`),
so the conversion is monotone. The vault's share path converts the truncated
(integer-valued) `Number` to an `.int64` `STAmount`. -/

/-- `STAmount.ofNumber` on an integral type is monotone for integer-valued
normalized inputs, in any rounding mode (the conversion is exact). -/
theorem STAmount.ofNumber_integral_toRat_mono (nt : NumericType)
    (n₁ n₂ : Number) (a₁ a₂ : STAmount) (mode₁ mode₂ : rounding_mode)
    (hnt : nt.isIntegral = true)
    (hn₁ : n₁.isNormalized) (hn₂ : n₂.isNormalized)
    (hden₁ : n₁.toRat.den = 1) (hden₂ : n₂.toRat.den = 1)
    (hok₁ : STAmount.ofNumber nt n₁ mode₁ = .ok a₁)
    (hok₂ : STAmount.ofNumber nt n₂ mode₂ = .ok a₂)
    (hle : n₁.toRat ≤ n₂.toRat) : a₁.toRat ≤ a₂.toRat := by
  rw [STAmount.ofNumber_integral_exact nt n₁ mode₁ a₁ hnt hn₁ hden₁ hok₁,
      STAmount.ofNumber_integral_exact nt n₂ mode₂ a₂ hnt hn₂ hden₂ hok₂]
  exact hle

/-! ## Layer 5: per-operation `to_nearest` monotonicity

Each `Number` arithmetic operation at `.to_nearest` produces the round-to-nearest
-even image of its exact value, i.e. `result.RoundsNearestEven <exact value>`.
Taking that characterization as a hypothesis, monotonicity in one argument is a
direct instance of `roundsNearestEven_mono` composed with monotonicity of the
exact operation. The sign split is explicit. A fixed factor `x` with
`0 ≤ x.toRat` gives left-monotonicity, a nonpositive factor gives
left-antitonicity.

The characterization hypothesis `result.RoundsNearestEven <exact value>` is what an
`operator_mul_x_y_.to_nearest = .ok result` bridge supplies, by identifying the
grid neighbours of the exact value with the algorithmic decomposition's mantissa
and its round decision (the fraction against `1/2`). That bridge is the remaining
step to make these unconditional. -/

/-- `operator_mul` is monotone in one factor at `.to_nearest` when the fixed factor
`x` is nonnegative: a larger second factor never rounds to a smaller product. -/
theorem operator_mul_left_toRat_mono (x y₁ y₂ r₁ r₂ : Number)
    (hne₁ : r₁.RoundsNearestEven (x.toRat * y₁.toRat))
    (hne₂ : r₂.RoundsNearestEven (x.toRat * y₂.toRat))
    (hx : 0 ≤ x.toRat) (hle : y₁.toRat ≤ y₂.toRat) :
    r₁.toRat ≤ r₂.toRat :=
  Number.roundsNearestEven_mono _ _ _ _ hne₁ hne₂ (by gcongr)

/-- `operator_mul` is antitone in one factor at `.to_nearest` when the fixed factor
`x` is nonpositive. -/
theorem operator_mul_left_toRat_anti (x y₁ y₂ r₁ r₂ : Number)
    (hne₁ : r₁.RoundsNearestEven (x.toRat * y₁.toRat))
    (hne₂ : r₂.RoundsNearestEven (x.toRat * y₂.toRat))
    (hx : x.toRat ≤ 0) (hle : y₁.toRat ≤ y₂.toRat) :
    r₂.toRat ≤ r₁.toRat :=
  Number.roundsNearestEven_mono _ _ _ _ hne₂ hne₁
    (by have := mul_le_mul_of_nonpos_left hle hx; linarith)

/-- `operator_div` is monotone in the numerator at `.to_nearest` for a fixed
positive denominator: a larger numerator never rounds to a smaller quotient. -/
theorem operator_div_num_toRat_mono (a₁ a₂ b r₁ r₂ : Number)
    (hne₁ : r₁.RoundsNearestEven (a₁.toRat / b.toRat))
    (hne₂ : r₂.RoundsNearestEven (a₂.toRat / b.toRat))
    (hb : 0 < b.toRat) (hle : a₁.toRat ≤ a₂.toRat) :
    r₁.toRat ≤ r₂.toRat :=
  Number.roundsNearestEven_mono _ _ _ _ hne₁ hne₂ (by gcongr)

/-- `operator_sub` is monotone in the minuend at `.to_nearest` (the withdraw NAV
path fixes the subtrahend): a larger `x` never rounds to a smaller difference. -/
theorem operator_sub_left_toRat_mono (x₁ x₂ y r₁ r₂ : Number)
    (hne₁ : r₁.RoundsNearestEven (x₁.toRat - y.toRat))
    (hne₂ : r₂.RoundsNearestEven (x₂.toRat - y.toRat))
    (hle : x₁.toRat ≤ x₂.toRat) :
    r₁.toRat ≤ r₂.toRat :=
  Number.roundsNearestEven_mono _ _ _ _ hne₁ hne₂ (by linarith)

/-- `operator_sub` is antitone in the subtrahend at `.to_nearest` (fixed minuend):
a larger `y` never rounds to a larger difference. -/
theorem operator_sub_right_toRat_anti (x y₁ y₂ r₁ r₂ : Number)
    (hne₁ : r₁.RoundsNearestEven (x.toRat - y₁.toRat))
    (hne₂ : r₂.RoundsNearestEven (x.toRat - y₂.toRat))
    (hle : y₁.toRat ≤ y₂.toRat) :
    r₂.toRat ≤ r₁.toRat :=
  Number.roundsNearestEven_mono _ _ _ _ hne₂ hne₁ (by linarith)

end XRPL.Model.Protocol
