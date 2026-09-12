import XRPL.Properties.Vault.Common.WithdrawPostSumMono
import XRPL.Properties.Vault.Common.RoundCanonical
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale

/-! # Downward withdrawal-clamp monotonicity

For a fractional withdrawal, `clampToSumExponent assetsTotal (-payout)` rounds
`payout` downward at the post-sum scale.  A larger payout selects a no-larger
scale, hence a grid at least as fine.  The core theorem below proves the needed
nested-decimal-grid fact directly from floor bounds and divisibility; it never
identifies a raw payout with its final clamped debit.

The executable corollaries intentionally separate the cases the current
rounding API exposes faithfully: nonzero fractional outputs use
`roundToExponent_rounded`; a zero lower output is discharged from downward
nonnegativity; integral negative clamps are exact sign-clearing passes.  The
remaining mixed case (a nonzero lower output and a zero upper output) needs the
missing zero-output floor characterization for scales in `[-81, 80]`; it is
not claimed here.
-/

namespace XRPL.Model.Protocol

/-- Downward decimal floors are monotone when the second grid is at least as
fine as the first.  The proof explicitly uses the integer factor
`10^(s₁ - s₂)` between the grids. -/
lemma downward_floor_mono_of_scale_le (x₁ x₂ : ℚ) (s₁ s₂ : ℤ)
    (hx : x₁ ≤ x₂) (hs : s₂ ≤ s₁) :
    (⌊x₁ / 10 ^ s₁⌋ : ℚ) * 10 ^ s₁ ≤
      (⌊x₂ / 10 ^ s₂⌋ : ℚ) * 10 ^ s₂ := by
  have hstep₂ : (0 : ℚ) < 10 ^ s₂ := zpow_pos (by norm_num) _
  have hd : 0 ≤ s₁ - s₂ := by omega
  let n : ℕ := 10 ^ (s₁ - s₂).toNat
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hdiff : (10 : ℚ) ^ (s₁ - s₂) = (n : ℚ) := by
    calc
      (10 : ℚ) ^ (s₁ - s₂) = (10 : ℚ) ^ ((s₁ - s₂).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hd]
      _ = (10 : ℚ) ^ (s₁ - s₂).toNat := zpow_natCast _ _
      _ = (n : ℚ) := by
        dsimp [n]
        norm_num
  have hpow : (10 : ℚ) ^ s₁ = (10 : ℚ) ^ s₂ * (n : ℚ) := by
    rw [show s₁ = s₂ + (s₁ - s₂) by omega,
      zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), hdiff]
  have hfloor₁₂ : ⌊x₁ / 10 ^ s₁⌋ ≤ ⌊x₂ / 10 ^ s₁⌋ :=
    Int.floor_mono
      (div_le_div_of_nonneg_right hx (le_of_lt (zpow_pos (by norm_num) _)))
  have hgrid : (⌊x₂ / 10 ^ s₁⌋ : ℚ) * 10 ^ s₁ ≤
      (⌊x₂ / 10 ^ s₂⌋ : ℚ) * 10 ^ s₂ := by
    have hk : (⌊x₂ / 10 ^ s₁⌋ * (n : ℤ) : ℤ) ≤ ⌊x₂ / 10 ^ s₂⌋ := by
      rw [hpow]
      apply Int.le_floor.mpr
      have hf : (⌊x₂ / (10 ^ s₂ * (n : ℚ))⌋ : ℚ) ≤
          x₂ / (10 ^ s₂ * (n : ℚ)) := Int.floor_le _
      rw [le_div_iff₀ hstep₂]
      have hf' := (le_div_iff₀ (mul_pos hstep₂ hnq)).mp hf
      convert hf' using 1 <;> push_cast <;> ring
    have hkq : ((⌊x₂ / 10 ^ s₁⌋ : ℤ) : ℚ) * (n : ℚ) ≤
        (⌊x₂ / 10 ^ s₂⌋ : ℚ) := by
      exact_mod_cast hk
    calc
      (⌊x₂ / 10 ^ s₁⌋ : ℚ) * 10 ^ s₁
          = ((⌊x₂ / 10 ^ s₁⌋ : ℚ) * (n : ℚ)) * 10 ^ s₂ := by
              rw [hpow]
              ring
      _ ≤ (⌊x₂ / 10 ^ s₂⌋ : ℚ) * 10 ^ s₂ :=
        mul_le_mul_of_nonneg_right hkq (le_of_lt hstep₂)
  calc
    (⌊x₁ / 10 ^ s₁⌋ : ℚ) * 10 ^ s₁ ≤
        (⌊x₂ / 10 ^ s₁⌋ : ℚ) * 10 ^ s₁ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hfloor₁₂)
        (le_of_lt (zpow_pos (by norm_num) _))
    _ ≤ (⌊x₂ / 10 ^ s₂⌋ : ℚ) * 10 ^ s₂ := hgrid

/-- Composition form for two successful nonzero fractional downward rounds.
The caller supplies the post-sum scale ordering (for example from
`Vault.postSumExponent_withdraw_antitone_strict` or its full-zero boundary
companion) and the two executable rounding results. -/
theorem STAmount.roundToExponent_downward_mono_of_scale_le
    (a₁ a₂ final₁ final₂ : STAmount) (s₁ s₂ : ℤ)
    (hc₁ : a₁.IOUCanonical) (hc₂ : a₂.IOUCanonical)
    (hs₁lo : (-81 : ℤ) ≤ s₁) (hs₁hi : s₁ ≤ 80)
    (hs₂lo : (-81 : ℤ) ≤ s₂) (hs₂hi : s₂ ≤ 80)
    (ha : a₁.toRat ≤ a₂.toRat) (hscale : s₂ ≤ s₁)
    (hfinal₁ : final₁.mValue ≠ 0) (hfinal₂ : final₂.mValue ≠ 0)
    (hround₁ : STAmount.roundToExponent a₁ s₁ .downward = .ok final₁)
    (hround₂ : STAmount.roundToExponent a₂ s₂ .downward = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  have hgrid₁ := STAmount.roundToExponent_rounded a₁ final₁ s₁ .downward
    hc₁ (by omega) hs₁hi hfinal₁ hround₁
  have hgrid₂ := STAmount.roundToExponent_rounded a₂ final₂ s₂ .downward
    hc₂ (by omega) hs₂hi hfinal₂ hround₂
  change final₁.toRat = (⌊a₁.toRat / 10 ^ s₁⌋ : ℚ) * 10 ^ s₁ at hgrid₁
  change final₂.toRat = (⌊a₂.toRat / 10 ^ s₂⌋ : ℚ) * 10 ^ s₂ at hgrid₂
  rw [hgrid₁, hgrid₂]
  exact downward_floor_mono_of_scale_le a₁.toRat a₂.toRat s₁ s₂ ha hscale

/-- If the smaller fractional clamp has already flushed to zero, its result is
below every successful nonnegative downward result.  This covers the zero-left
branch without treating raw payout and final debit as equal. -/
theorem STAmount.roundToExponent_downward_zero_left_le
    (a₂ final₁ final₂ : STAmount) (s₂ : ℤ)
    (hc₂ : a₂.IOUCanonical) (hs₂lo : (-96 : ℤ) ≤ s₂) (hs₂hi : s₂ ≤ 80)
    (ha₂ : 0 ≤ a₂.toRat) (hzero₁ : final₁.mValue = 0)
    (hround₂ : STAmount.roundToExponent a₂ s₂ .downward = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  have hnonneg := STAmount.roundToExponent_downward_nonneg a₂ final₂ s₂ hc₂
    hs₂lo hs₂hi ha₂ hround₂
  have hzero : final₁.toRat = 0 := by
    rw [STAmount.toRat_signed, hzero₁]
    simp
  rw [hzero]
  exact hnonneg

/-- At a canonical scale, the zero sentinel is exactly the downward floor-zero
case. This is obtained from the successful call's exact grid result, rather
than assuming a range or interpreting a raw amount as its clamped debit. -/
theorem STAmount.roundToExponent_downward_zero_iff_floor_zero
    (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-81 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    result.mValue = 0 ↔ ⌊value.toRat / 10 ^ s⌋ = 0 := by
  have hgrid := STAmount.roundToExponent_downward_rounded_at_canonical_scale
    value result s hc hs_lo hs_hi hok
  constructor
  · intro hzero
    have hvalue : result.toRat = 0 := by
      rw [STAmount.toRat_signed, hzero]
      simp
    rw [hgrid] at hvalue
    have hpow : (10 : ℚ) ^ s ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
    have hfloor : (⌊value.toRat / 10 ^ s⌋ : ℚ) = 0 :=
      (mul_eq_zero.mp hvalue).resolve_right hpow
    exact_mod_cast hfloor
  · intro hfloor
    have hvalue : result.toRat = 0 := by rw [hgrid, hfloor]; norm_num
    by_contra hnonzero
    exact (STAmount.toRat_ne_zero result hnonzero) hvalue

/-- Total downward-grid monotonicity at canonical IOU scales. Unlike the older
nonzero/nonzero and zero-left lemmas, this theorem has no output-status
premises: the exact successful-round characterization also covers a right-hand
zero sentinel. -/
theorem STAmount.roundToExponent_downward_mono_of_canonical_scales
    (a₁ a₂ final₁ final₂ : STAmount) (s₁ s₂ : ℤ)
    (hc₁ : a₁.IOUCanonical) (hc₂ : a₂.IOUCanonical)
    (hs₁lo : (-81 : ℤ) ≤ s₁) (hs₁hi : s₁ ≤ 80)
    (hs₂lo : (-81 : ℤ) ≤ s₂) (hs₂hi : s₂ ≤ 80)
    (ha : a₁.toRat ≤ a₂.toRat) (hscale : s₂ ≤ s₁)
    (hround₁ : STAmount.roundToExponent a₁ s₁ .downward = .ok final₁)
    (hround₂ : STAmount.roundToExponent a₂ s₂ .downward = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  have hgrid₁ := STAmount.roundToExponent_downward_rounded_at_canonical_scale
    a₁ final₁ s₁ hc₁ hs₁lo hs₁hi hround₁
  have hgrid₂ := STAmount.roundToExponent_downward_rounded_at_canonical_scale
    a₂ final₂ s₂ hc₂ hs₂lo hs₂hi hround₂
  rw [hgrid₁, hgrid₂]
  exact downward_floor_mono_of_scale_le a₁.toRat a₂.toRat s₁ s₂ ha hscale

/-- A successful fractional round at or below the input exponent takes the
executable identity branch. This derives the `-100` sentinel behavior from the
successful call and canonical exponent bounds, not from a raw/final equation. -/
theorem STAmount.roundToExponent_eq_self_of_scale_le_exponent
    (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs : s ≤ value.exponent)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    result = value := by
  have hint : value.integral = false := by
    unfold STAmount.integral
    rw [hc.is_fractional]
    rfl
  have hmv : value.mValue ≠ 0 := by
    intro hzero
    have hnat : value.mValue.toNat = 0 := by rw [hzero]; rfl
    have := hc.mant_lo
    omega
  have hzero : ¬ value.isZero = true := by
    unfold STAmount.isZero
    rw [beq_eq_false_iff_ne.mpr hmv]
    exact Bool.false_ne_true
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [hint]; exact Bool.false_ne_true), if_neg hzero, if_pos hs] at hok
  exact (Except.ok.inj hok).symm

/-- Total successful downward-round monotonicity for the withdrawal post-sum
scale domain. The right scale is either a canonical IOU grid or the actual
`-100` zero sentinel returned by a successful full-post-sum calculation. The
sentinel branch is an executable identity round; canonical grids use the exact
floor theorem, including zero outputs. -/
theorem STAmount.roundToExponent_downward_mono_of_scale_le_total
    (a₁ a₂ final₁ final₂ : STAmount) (s₁ s₂ : ℤ)
    (hc₁ : a₁.IOUCanonical) (hc₂ : a₂.IOUCanonical)
    (hs₁lo : (-96 : ℤ) ≤ s₁) (hs₁hi : s₁ ≤ 80)
    (hs₂hi : s₂ ≤ 80) (hs₂domain : s₂ = -100 ∨ (-81 : ℤ) ≤ s₂)
    (hnonneg₁ : 0 ≤ a₁.toRat) (ha : a₁.toRat ≤ a₂.toRat) (hscale : s₂ ≤ s₁)
    (hround₁ : STAmount.roundToExponent a₁ s₁ .downward = .ok final₁)
    (hround₂ : STAmount.roundToExponent a₂ s₂ .downward = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  rcases hs₂domain with hs₂ | hs₂
  · have hs₂exp : s₂ ≤ a₂.exponent := by
      rw [hs₂]
      exact le_trans (by norm_num) hc₂.exp_lo
    have hfinal₂ := STAmount.roundToExponent_eq_self_of_scale_le_exponent
      a₂ final₂ s₂ hc₂ hs₂exp hround₂
    rw [hfinal₂]
    exact le_trans
      (STAmount.roundToExponent_downward_le a₁ final₁ s₁ hc₁ hs₁lo hs₁hi hnonneg₁ hround₁) ha
  · have hs₁lo : (-81 : ℤ) ≤ s₁ := le_trans hs₂ hscale
    exact STAmount.roundToExponent_downward_mono_of_canonical_scales
      a₁ a₂ final₁ final₂ s₁ s₂ hc₁ hc₂ hs₁lo hs₁hi hs₂ hs₂hi ha hscale hround₁ hround₂

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Source-path composition for the fractional negative-clamp branch. The two
`hround` facts are the direct reductions obtained by unfolding the successful
`clampToSumExponent assetsTotal a.operator_neg` executions through their
successful `postSumExponent` binds. Keeping them explicit makes this theorem
usable before the withdrawal reduction layer has a reusable bind-peeling lemma.
The clamp hypotheses retain the executable final-debit contract; no equality
between `aᵢ` and `finalᵢ` is assumed. -/
theorem Vault.clampToSumExponent_withdraw_fractional_mono_of_rounds
    (v : Vault) (a₁ a₂ final₁ final₂ : STAmount) (s₁ s₂ : ℤ)
    (hc₁ : a₁.IOUCanonical) (hc₂ : a₂.IOUCanonical)
    (hs₁lo : (-81 : ℤ) ≤ s₁) (hs₁hi : s₁ ≤ 80)
    (hs₂lo : (-81 : ℤ) ≤ s₂) (hs₂hi : s₂ ≤ 80)
    (ha : a₁.toRat ≤ a₂.toRat) (hscale : s₂ ≤ s₁)
    (hfinal₁ : final₁.mValue ≠ 0) (hfinal₂ : final₂.mValue ≠ 0)
    (_hclamp₁ : clampToSumExponent v.assetsTotal a₁.operator_neg = .ok final₁)
    (_hclamp₂ : clampToSumExponent v.assetsTotal a₂.operator_neg = .ok final₂)
    (hround₁ : STAmount.roundToExponent a₁ s₁ .downward = .ok final₁)
    (hround₂ : STAmount.roundToExponent a₂ s₂ .downward = .ok final₂) :
    final₁.toRat ≤ final₂.toRat :=
  STAmount.roundToExponent_downward_mono_of_scale_le a₁ a₂ final₁ final₂ s₁ s₂
    hc₁ hc₂ hs₁lo hs₁hi hs₂lo hs₂hi ha hscale hfinal₁ hfinal₂ hround₁ hround₂

/-- Total composition for successful fractional negative clamps. The supplied
clamp equations describe the real raw-to-final executions; the proof never
rewrites a raw payout into a final debit. All output-zero cases are discharged
by `roundToExponent_downward_mono_of_scale_le_total`. -/
theorem Vault.clampToSumExponent_withdraw_fractional_mono_of_rounds_total
    (v : Vault) (a₁ a₂ final₁ final₂ : STAmount) (s₁ s₂ : ℤ)
    (hc₁ : a₁.IOUCanonical) (hc₂ : a₂.IOUCanonical)
    (hs₁lo : (-96 : ℤ) ≤ s₁) (hs₁hi : s₁ ≤ 80)
    (hs₂hi : s₂ ≤ 80) (hs₂domain : s₂ = -100 ∨ (-81 : ℤ) ≤ s₂)
    (hnonneg₁ : 0 ≤ a₁.toRat) (ha : a₁.toRat ≤ a₂.toRat) (hscale : s₂ ≤ s₁)
    (_hclamp₁ : clampToSumExponent v.assetsTotal a₁.operator_neg = .ok final₁)
    (_hclamp₂ : clampToSumExponent v.assetsTotal a₂.operator_neg = .ok final₂)
    (hround₁ : STAmount.roundToExponent a₁ s₁ .downward = .ok final₁)
    (hround₂ : STAmount.roundToExponent a₂ s₂ .downward = .ok final₂) :
    final₁.toRat ≤ final₂.toRat :=
  STAmount.roundToExponent_downward_mono_of_scale_le_total a₁ a₂ final₁ final₂ s₁ s₂
    hc₁ hc₂ hs₁lo hs₁hi hs₂hi hs₂domain hnonneg₁ ha hscale hround₁ hround₂

end XRPL.Model.SingleAssetVault


namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Source-path adapters

The public withdrawal reduction exposes a successful `clampToSumExponent` call,
but the fractional negative branch contains two further executable binds: the
post-sum scale and the directed round.  These lemmas peel exactly those binds.
The negative-bit premise is intentional: a canonical positive raw payout enters
this branch after `operator_neg`; a signed zero instead follows the executable
nonnegative-delta branch and must not be described as a direct round.
-/

/-- A successful fractional negative clamp exposes its actual post-sum scale and
its direct downward-round equation.  No relationship between `raw` and `final`
is asserted. -/
theorem Vault.clampToSumExponent_withdraw_fractional_steps
    (v : Vault) (raw final : STAmount)
    (hfrac : raw.integral = false)
    (hnonzero : raw.mValue ≠ 0)
    (hnegative : raw.operator_neg.negative = true)
    (hclamp : clampToSumExponent v.assetsTotal raw.operator_neg = .ok final) :
    ∃ scale : Int,
      postSumExponent v.assetsTotal raw.operator_neg = .ok scale ∧
      STAmount.roundToExponent raw scale .downward = .ok final := by
  unfold clampToSumExponent at hclamp
  rw [show raw.operator_neg.integral = false by
        change raw.operator_neg.mNumericType.isIntegral = false
        rw [STAmount.operator_neg_mNumericType]
        exact hfrac,
      hnegative] at hclamp
  have hzero : (raw.mValue == 0) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hnonzero (beq_iff_eq.mp h)
  have hdouble : raw.operator_neg.operator_neg = raw := by
    simp [STAmount.operator_neg, hzero]
  simp only [pure_bind] at hclamp
  obtain ⟨scale, hpost, hround⟩ := bind_ok_peel _ _ _ hclamp
  refine ⟨scale, hpost, ?_⟩
  simpa [hnegative, hdouble] using hround

/-- An integral withdrawal clamp is the executable sign-clearing branch.  The
returned record is precisely the branch-selected absolute delta. -/
theorem Vault.clampToSumExponent_withdraw_integral_sign_clear
    (v : Vault) (raw final : STAmount)
    (hintegral : raw.integral = true)
    (hclamp : clampToSumExponent v.assetsTotal raw.operator_neg = .ok final) :
    final =
      if raw.operator_neg.negative then raw.operator_neg.operator_neg else raw.operator_neg := by
  unfold clampToSumExponent at hclamp
  rw [show raw.operator_neg.integral = true by
        change raw.operator_neg.mNumericType.isIntegral = true
        rw [STAmount.operator_neg_mNumericType]
        exact hintegral] at hclamp
  exact (Except.ok.inj hclamp).symm

/-- Truthful integral transport: the executable integral clamp sign-clears its
negative delta, and nonnegative raw payouts make that branch value-preserving.
The proof handles both ordinary double-negation and signed-zero behavior
without equating raw and final records. -/
theorem Vault.clampToSumExponent_withdraw_integral_mono
    (v : Vault) (raw₁ raw₂ final₁ final₂ : STAmount)
    (hint₁ : raw₁.integral = true) (hint₂ : raw₂.integral = true)
    (hraw : raw₁.toRat ≤ raw₂.toRat)
    (hnonneg₁ : 0 ≤ raw₁.toRat) (hnonneg₂ : 0 ≤ raw₂.toRat)
    (hclamp₁ : clampToSumExponent v.assetsTotal raw₁.operator_neg = .ok final₁)
    (hclamp₂ : clampToSumExponent v.assetsTotal raw₂.operator_neg = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  have hsign_or_zero : ∀ raw : STAmount, 0 ≤ raw.toRat →
      raw.operator_neg.negative = true ∨ raw.toRat = 0 := by
    intro raw hnonneg
    by_cases hnegative : raw.operator_neg.negative = true
    · exact Or.inl hnegative
    · right
      have hnegative_false : raw.operator_neg.negative = false :=
        Bool.eq_false_of_not_eq_true hnegative
      by_cases hzero : raw.mValue = 0
      · exact STAmount.toRat_eq_zero_of_mValue_zero raw hzero
      · have hbeq : (raw.mValue == 0) = false := beq_eq_false_iff_ne.mpr hzero
        have hraw_negative : raw.mIsNegative = true := by
          unfold STAmount.operator_neg at hnegative_false
          rw [hbeq] at hnegative_false
          change (!raw.mIsNegative) = false at hnegative_false
          cases hraw : raw.mIsNegative <;> simp [hraw] at hnegative_false ⊢
        have hnat_ne : raw.mValue.toNat ≠ 0 := by
          intro hnat
          apply hzero
          exact UInt64.toNat_inj.mp hnat
        have hnat : 0 < raw.mValue.toNat := Nat.pos_of_ne_zero hnat_ne
        have hpow : 0 < (10 : ℚ) ^ raw.mOffset := zpow_pos (by norm_num) _
        have hproduct : 0 < (raw.mValue.toNat : ℚ) * 10 ^ raw.mOffset :=
          mul_pos (by exact_mod_cast hnat) hpow
        rw [STAmount.toRat_of_neg raw hraw_negative] at hnonneg
        linarith
  have hclear₁ := hsign_or_zero raw₁ hnonneg₁
  have hclear₂ := hsign_or_zero raw₂ hnonneg₂
  have hvalue : ∀ raw : STAmount,
      raw.operator_neg.negative = true ∨ raw.toRat = 0 →
      (if raw.operator_neg.negative then raw.operator_neg.operator_neg
        else raw.operator_neg).toRat = raw.toRat := by
    intro raw hclear
    rcases hclear with hneg | hzero
    · rw [if_pos hneg, STAmount.operator_neg_toRat, STAmount.operator_neg_toRat]
      ring
    · cases hbit : raw.operator_neg.negative with
      | false =>
        rw [if_neg (by simp [hbit]), STAmount.operator_neg_toRat, hzero]
        ring
      | true =>
        rw [if_pos (by simp [hbit]), STAmount.operator_neg_toRat, STAmount.operator_neg_toRat]
        ring
  have hfinal₁ := Vault.clampToSumExponent_withdraw_integral_sign_clear
    v raw₁ final₁ hint₁ hclamp₁
  have hfinal₂ := Vault.clampToSumExponent_withdraw_integral_sign_clear
    v raw₂ final₂ hint₂ hclamp₂
  rw [hfinal₁, hfinal₂, hvalue raw₁ hclear₁, hvalue raw₂ hclear₂]
  exact hraw

/-- Directly usable dynamic-grid transport once the source-path clamp adapters
have exposed the post-sum scales.  This is the cycle-41 total floor theorem
applied to the real successful clamps, rather than to assumed raw/final
identities. -/
theorem Vault.clampToSumExponent_withdraw_fractional_mono
    (v : Vault) (raw₁ raw₂ final₁ final₂ : STAmount) (s₁ s₂ : Int)
    (hc₁ : raw₁.IOUCanonical) (hc₂ : raw₂.IOUCanonical)
    (hs₁lo : (-96 : Int) ≤ s₁) (hs₁hi : s₁ ≤ 80)
    (hs₂hi : s₂ ≤ 80) (hs₂domain : s₂ = -100 ∨ (-81 : Int) ≤ s₂)
    (hnonneg₁ : 0 ≤ raw₁.toRat) (hraw : raw₁.toRat ≤ raw₂.toRat)
    (hscale : s₂ ≤ s₁)
    (hpost₁_expected : postSumExponent v.assetsTotal raw₁.operator_neg = .ok s₁)
    (hpost₂_expected : postSumExponent v.assetsTotal raw₂.operator_neg = .ok s₂)
    (hneg₁ : raw₁.operator_neg.negative = true)
    (hneg₂ : raw₂.operator_neg.negative = true)
    (hclamp₁ : clampToSumExponent v.assetsTotal raw₁.operator_neg = .ok final₁)
    (hclamp₂ : clampToSumExponent v.assetsTotal raw₂.operator_neg = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  obtain ⟨scale₁, hpost₁, hround₁⟩ :=
    Vault.clampToSumExponent_withdraw_fractional_steps v raw₁ final₁
      (by
        change raw₁.mNumericType.isIntegral = false
        rw [hc₁.is_fractional]
        decide)
      (by
        intro hzero
        have hnat : raw₁.mValue.toNat = 0 := by simp [hzero]
        have := hc₁.mant_lo
        omega) hneg₁ hclamp₁
  obtain ⟨scale₂, hpost₂, hround₂⟩ :=
    Vault.clampToSumExponent_withdraw_fractional_steps v raw₂ final₂
      (by
        change raw₂.mNumericType.isIntegral = false
        rw [hc₂.is_fractional]
        decide)
      (by
        intro hzero
        have hnat : raw₂.mValue.toNat = 0 := by simp [hzero]
        have := hc₂.mant_lo
        omega) hneg₂ hclamp₂
  have hs₁ : scale₁ = s₁ := Except.ok.inj (hpost₁.symm.trans hpost₁_expected)
  have hs₂ : scale₂ = s₂ := Except.ok.inj (hpost₂.symm.trans hpost₂_expected)
  subst scale₁
  subst scale₂
  exact Vault.clampToSumExponent_withdraw_fractional_mono_of_rounds_total
    v raw₁ raw₂ final₁ final₂ s₁ s₂ hc₁ hc₂ hs₁lo hs₁hi hs₂hi hs₂domain
    hnonneg₁ hraw hscale hclamp₁ hclamp₂ hround₁ hround₂
/-- Strict in-funds source-path composition. The successful clamp equations are
peeled into direct rounds, cycle-39 orders their dynamic post-sum scales, and
cycle-41 transports the raw payout order across those actual rounds. -/
theorem Vault.clampToSumExponent_withdraw_fractional_mono_strict
    (v : Vault) (raw₁ raw₂ final₁ final₂ : STAmount)
    (debit₁ debit₂ sum₁ sum₂ : Number) (post₁ post₂ : STAmount) (s₁ s₂ : Int)
    (hc₁ : raw₁.IOUCanonical) (hc₂ : raw₂.IOUCanonical)
    (hraw₁_nonneg : 0 ≤ raw₁.toRat) (hraw₂_nonneg : 0 ≤ raw₂.toRat)
    (hraw : raw₁.toRat ≤ raw₂.toRat)
    (hfunds : raw₂.toRat ≤ v.assetsAvailable.toRat)
    (hstrict : raw₂.toRat < v.assetsTotal.toRat)
    (hto₁ : raw₁.operator_neg.toNumber .to_nearest = .ok debit₁)
    (hto₂ : raw₂.operator_neg.toNumber .to_nearest = .ok debit₂)
    (hdebit₁_value : debit₁.toRat = -raw₁.toRat)
    (hdebit₂_value : debit₂.toRat = -raw₂.toRat)
    (hdebit₁_norm : debit₁.isNormalized) (hdebit₂_norm : debit₂.isNormalized)
    (hadd₁ : v.assetsTotal.operator_add debit₁ .to_nearest = .ok sum₁)
    (hadd₂ : v.assetsTotal.operator_add debit₂ .to_nearest = .ok sum₂)
    (hsum₁_pos : 0 < sum₁.toRat) (hsum₂_pos : 0 < sum₂.toRat)
    (hadd_gap : v.assetsTotal.toRat + debit₂.toRat < v.assetsTotal.toRat + debit₁.toRat →
      v.assetsTotal.toRat + debit₂.toRat ≤ (maxRepNat : ℚ) *
        ((v.assetsTotal.toRat + debit₁.toRat) - (v.assetsTotal.toRat + debit₂.toRat)))
    (hsum₁_range : sum₁.exponent_ + 4 ≤ maxExponent)
    (hsum₂_range : sum₂.exponent_ + 4 ≤ maxExponent)
    (hof₁ : STAmount.ofNumber .fractional sum₁ .to_nearest = .ok post₁)
    (hof₂ : STAmount.ofNumber .fractional sum₂ .to_nearest = .ok post₂)
    (hpost₁_nonzero : post₁.mValue ≠ 0) (hpost₂_nonzero : post₂.mValue ≠ 0)
    (hpost₁ : postSumExponent v.assetsTotal raw₁.operator_neg = .ok s₁)
    (hpost₂ : postSumExponent v.assetsTotal raw₂.operator_neg = .ok s₂)
    (hs₁lo : (-96 : Int) ≤ s₁) (hs₁hi : s₁ ≤ 80)
    (hs₂hi : s₂ ≤ 80) (hs₂domain : s₂ = -100 ∨ (-81 : Int) ≤ s₂)
    (hneg₁ : raw₁.operator_neg.negative = true)
    (hneg₂ : raw₂.operator_neg.negative = true)
    (hclamp₁ : clampToSumExponent v.assetsTotal raw₁.operator_neg = .ok final₁)
    (hclamp₂ : clampToSumExponent v.assetsTotal raw₂.operator_neg = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  have hscale := Vault.postSumExponent_withdraw_antitone_strict
    v raw₁ raw₂ debit₁ debit₂ sum₁ sum₂ post₁ post₂ s₁ s₂
    hc₁.is_fractional hc₂.is_fractional hraw₁_nonneg hraw₂_nonneg hraw hfunds hstrict
    hto₁ hto₂ hdebit₁_value hdebit₂_value hdebit₁_norm hdebit₂_norm hadd₁ hadd₂
    hsum₁_pos hsum₂_pos hadd_gap hsum₁_range hsum₂_range hof₁ hof₂
    hpost₁_nonzero hpost₂_nonzero hpost₁ hpost₂
  exact Vault.clampToSumExponent_withdraw_fractional_mono
    v raw₁ raw₂ final₁ final₂ s₁ s₂ hc₁ hc₂ hs₁lo hs₁hi hs₂hi hs₂domain
    hraw₁_nonneg hraw hscale hpost₁ hpost₂ hneg₁ hneg₂ hclamp₁ hclamp₂

/-- Exact-full source-path composition. The cycle-39 full-zero theorem supplies
the real `-100` post-sum sentinel; cycle-41 then uses its executable identity
round branch rather than treating that sentinel as an ordinary IOU grid. -/
theorem Vault.clampToSumExponent_withdraw_fractional_mono_full_zero
    (v : Vault) (raw₁ raw₂ final₁ final₂ : STAmount)
    (debit₁ debit₂ sum₁ : Number) (s₁ s₂ : Int)
    (hc₁ : raw₁.IOUCanonical) (hc₂ : raw₂.IOUCanonical)
    (hraw₁_nonneg : 0 ≤ raw₁.toRat) (hraw₂_nonneg : 0 ≤ raw₂.toRat)
    (hraw : raw₁.toRat ≤ raw₂.toRat)
    (hfunds : raw₂.toRat ≤ v.assetsAvailable.toRat)
    (hfull : raw₂.toRat = v.assetsTotal.toRat)
    (hto₁ : raw₁.operator_neg.toNumber .to_nearest = .ok debit₁)
    (hto₂ : raw₂.operator_neg.toNumber .to_nearest = .ok debit₂)
    (hadd₁ : v.assetsTotal.operator_add debit₁ .to_nearest = .ok sum₁)
    (hadd₂_zero : v.assetsTotal.operator_add debit₂ .to_nearest = .ok Number.zero)
    (hpost₁ : postSumExponent v.assetsTotal raw₁.operator_neg = .ok s₁)
    (hpost₂ : postSumExponent v.assetsTotal raw₂.operator_neg = .ok s₂)
    (hs₁lo : (-96 : Int) ≤ s₁) (hs₁hi : s₁ ≤ 80) (hs₂hi : s₂ ≤ 80)
    (hneg₁ : raw₁.operator_neg.negative = true)
    (hneg₂ : raw₂.operator_neg.negative = true)
    (hclamp₁ : clampToSumExponent v.assetsTotal raw₁.operator_neg = .ok final₁)
    (hclamp₂ : clampToSumExponent v.assetsTotal raw₂.operator_neg = .ok final₂) :
    final₁.toRat ≤ final₂.toRat := by
  obtain ⟨hsentinel, hscale⟩ := Vault.postSumExponent_withdraw_full_zero_antitone
    v raw₁ raw₂ debit₁ debit₂ sum₁ s₁ s₂
    hc₁.is_fractional hc₂.is_fractional hraw₁_nonneg hraw₂_nonneg hraw hfunds hfull
    hto₁ hto₂ hadd₁ hadd₂_zero hpost₁ hpost₂
  exact Vault.clampToSumExponent_withdraw_fractional_mono
    v raw₁ raw₂ final₁ final₂ s₁ s₂ hc₁ hc₂ hs₁lo hs₁hi hs₂hi (Or.inl hsentinel)
    hraw₁_nonneg hraw hscale hpost₁ hpost₂ hneg₁ hneg₂ hclamp₁ hclamp₂

end XRPL.Model.SingleAssetVault
