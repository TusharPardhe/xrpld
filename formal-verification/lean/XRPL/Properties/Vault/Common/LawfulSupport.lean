import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.NumberBridge
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.ClawbackReduction
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultBurn

/-! # Support lemmas for the vault lawfulness-preservation proofs

Four groups:

* rational bookkeeping for integer-valued `ℚ` values (`den = 1`);
* the zero-record shape chain: every mantissa-`0` output of
  `Guard.bringIntoRange` / `Guard.doRoundUp` / `doNormalize128` /
  `Number.operator_add` (on normalized operands) is the literal `Number.zero`,
  which upgrades the bridge normalization lemmas to unconditional form;
* `STAmount` canonical-shape exactness for `toNumber` / `ofNumber .int64`;
* success-path reductions for `Vault.withdraw` / `Vault.clawback` and the
  asset-parity (`assetsAvailable = assetsTotal`) preservation walks. -/

namespace XRPL.Model.Protocol

/-! ## Rational bookkeeping -/

/-- An integer-valued rational is the cast of its numerator. -/
lemma rat_eq_num_cast_of_den_one (q : ℚ) (hden : q.den = 1) : ((q.num : ℤ) : ℚ) = q := by
  conv_rhs => rw [← Rat.num_div_den q]
  rw [hden, Nat.cast_one, div_one]

/-- A non-negative integer-valued rational is recovered from `q.num.toNat`. -/
lemma rat_toNat_cast_of_den_one (q : ℚ) (hden : q.den = 1) (h0 : 0 ≤ q) :
    ((q.num.toNat : ℕ) : ℚ) = q := by
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum]
  exact rat_eq_num_cast_of_den_one q hden

/-- Numerator magnitude bound for a small non-negative integer-valued rational. -/
lemma rat_num_natAbs_lt_of_le (q : ℚ) (hden : q.den = 1) (h0 : 0 ≤ q)
    (hle : q ≤ 2 ^ 63 - 1) : q.num.natAbs < 2 ^ 63 := by
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  have hcast := rat_eq_num_cast_of_den_one q hden
  have hle' : ((q.num : ℤ) : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by
    rw [hcast]; exact le_trans hle (by norm_num)
  have hz : q.num ≤ 2 ^ 63 - 1 := by exact_mod_cast hle'
  omega

/-- An integer within distance `< 1` of an integer-valued rational equals it. -/
lemma int_cast_eq_of_abs_lt_one (a : ℤ) (q : ℚ) (hden : q.den = 1)
    (h : |(a : ℚ) - q| < 1) : (a : ℚ) = q := by
  have hcast := rat_eq_num_cast_of_den_one q hden
  rw [← hcast] at h ⊢
  have h' : |((a - q.num : ℤ) : ℚ)| < 1 := by push_cast; exact h
  have hz : (a - q.num : ℤ).natAbs < 1 := by
    have := (abs_lt.mp h')
    have h1 : ((a - q.num : ℤ) : ℚ) < 1 := this.2
    have h2 : (-1 : ℚ) < ((a - q.num : ℤ) : ℚ) := this.1
    have h1' : (a - q.num : ℤ) < 1 := by exact_mod_cast h1
    have h2' : (-1 : ℤ) < (a - q.num : ℤ) := by exact_mod_cast h2
    omega
  have : a = q.num := by omega
  rw [this]

/-- Integer-valued rationals add to the cast of the numerator sum. -/
lemma rat_add_eq_num_cast (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) :
    a + b = ((a.num + b.num : ℤ) : ℚ) := by
  conv_lhs => rw [← rat_eq_num_cast_of_den_one a ha, ← rat_eq_num_cast_of_den_one b hb]
  push_cast; ring

/-- Integer-valued rationals subtract to the cast of the numerator difference. -/
lemma rat_sub_eq_num_cast (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) :
    a - b = ((a.num - b.num : ℤ) : ℚ) := by
  conv_lhs => rw [← rat_eq_num_cast_of_den_one a ha, ← rat_eq_num_cast_of_den_one b hb]
  push_cast; ring

/-- A gap between distinct integer-valued rationals is at least one. -/
lemma rat_one_le_sub_of_lt (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) (h : b < a) :
    1 ≤ a - b := by
  rw [rat_sub_eq_num_cast a b ha hb]
  have hnum : b.num < a.num := by
    have h1 : ((b.num : ℤ) : ℚ) < ((a.num : ℤ) : ℚ) := by
      rw [rat_eq_num_cast_of_den_one a ha, rat_eq_num_cast_of_den_one b hb]; exact h
    exact_mod_cast h1
  have : (1 : ℤ) ≤ a.num - b.num := by omega
  exact_mod_cast this

/-! ## Number sign bookkeeping -/

/-- A normalized `Number` with non-negative value has a clear sign bit. -/
lemma Number.negative_false_of_normalized_nonneg (n : Number) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) : n.negative_ = false := by
  rcases hneg : n.negative_ with _ | _
  · rfl
  · exfalso
    rcases hn with hz | ⟨hmin, _, _, _, _⟩
    · rw [hz] at hneg; exact absurd hneg (by decide)
    · have hm_ne : n.mantissa_ ≠ 0 := by
        intro h
        rw [UInt64.le_iff_toNat_le, largeRange_min_val] at hmin
        have : n.mantissa_.toNat = 0 := by rw [h]; rfl
        omega
      have hlt : n.toRat < 0 :=
        lt_of_le_of_ne (Number.toRat_nonpos_of_negative n hneg)
          (Number.toRat_ne_zero_of_mantissa_ne_zero n hm_ne)
      linarith

/-! ## Zero-record shape chain -/

/-- `bringIntoRange` output: the canonical zero record, or nonzero mantissa. -/
lemma Guard.bringIntoRange_cases (neg : Bool) (m : UInt64) (e : Int) (minM : UInt64) :
    Guard.bringIntoRange neg m e minM
      = ({ negative_ := false, mantissa_ := 0, exponent_ := -2147483648 } : RoundResult) ∨
    (Guard.bringIntoRange neg m e minM).mantissa_ ≠ 0 := by
  unfold Guard.bringIntoRange
  rcases hp : (if m < minM ∧ m ≠ 0 then (m * 10, e - 1) else (m, e)) with ⟨m', e'⟩
  dsimp only
  by_cases hz : e' < minExponent ∨ m' = 0
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    push_neg at hz
    exact Or.inr hz.2

/-- A mantissa-`0` `doRoundUp` result converts to the literal `Number.zero`. -/
lemma Guard.doRoundUp_zero_shape (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res)
    (h0 : res.mantissa_ = 0) : res.toNumber = Number.zero := by
  have key : ∃ (n' : Bool) (m' : UInt64) (e' : Int),
      res = Guard.bringIntoRange n' m' e' minM := by
    unfold Guard.doRoundUp Guard.doDropDigit at hok
    dsimp only at hok
    repeat' split at hok
    all_goals
      first
      | exact ⟨_, _, _, (Except.ok.inj hok).symm⟩
      | simp at hok
  obtain ⟨n', m', e', hres⟩ := key
  rcases Guard.bringIntoRange_cases n' m' e' minM with hc | hc
  · rw [hres, hc]; rfl
  · rw [← hres] at hc
    exact absurd h0 hc

/-- A mantissa-`0` `doNormalize128` result is the literal `Number.zero`. -/
lemma doNormalize128_zero_shape (zn : Bool) (M : UInt128) (e : Int) (sticky : Bool)
    (mode : rounding_mode) (result : Number)
    (hok : doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  unfold doNormalize128 at hok
  by_cases hM : (M == 0) = true
  · rw [if_pos hM] at hok
    exact (Except.ok.inj hok).symm
  · rw [if_neg hM] at hok
    simp only [] at hok
    rcases hsu : doNormalize128.scaleUp largeRange.min M e with ⟨M₁, e₁⟩
    rw [hsu] at hok
    simp only [] at hok
    set g₀ : Guard := (if sticky = true
        then (if zn then Guard.new.set_negative else Guard.new).set_sticky
        else (if zn then Guard.new.set_negative else Guard.new)) with hg₀_def
    cases hsd : doNormalize_scaleDown128 largeRange.max M₁ e₁ g₀ with
    | error err => rw [hsd] at hok; simp at hok
    | ok sd =>
      obtain ⟨m₂, e₂, g₂⟩ := sd
      rw [hsd] at hok
      simp only [] at hok
      by_cases hund : (e₂ < minExponent || m₂ < toUInt128 largeRange.min) = true
      · rw [if_pos hund] at hok
        exact (Except.ok.inj hok).symm
      · rw [if_neg hund] at hok
        cases hcap : doNormalize_capAtMaxRep (toUInt64 m₂) e₂ g₂ with
        | error err => rw [hcap] at hok; simp at hok
        | ok cp =>
          obtain ⟨m₃, e₃, g₃⟩ := cp
          rw [hcap] at hok
          simp only [] at hok
          cases hru : g₃.doRoundUp zn m₃ e₃ largeRange.min largeRange.max mode
              .normalize2 with
          | error err => rw [hru] at hok; simp at hok
          | ok res =>
            rw [hru] at hok
            simp only [] at hok
            have hres : result = res.toNumber := (Except.ok.inj hok).symm
            have hres0 : res.mantissa_ = 0 := by
              rw [hres] at h0; exact h0
            rw [hres]
            exact Guard.doRoundUp_zero_shape g₃ zn m₃ e₃ largeRange.min largeRange.max mode
              .normalize2 res hru hres0

/-- A mantissa-`0` `to_nearest` addition result of normalized operands is the
literal `Number.zero`. -/
lemma Number.operator_add_zero_shape (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hx h0
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hy h0
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · unfold Number.operator_add at hok
    rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
    exact (Except.ok.inj
      (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
  have hx_mant_ne : x.mantissa_ ≠ 0 := by
    intro h
    exact hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hy_mant_ne : y.mantissa_ ≠ 0 := by
    intro h
    exact hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  by_cases h_sign_eq : x.negative_ = y.negative_
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hresult_ne, _, _⟩ :=
      operator_add_algorithmic_facts_same_sign_to_nearest x y result hx hy hx_mant_ne hy_mant_ne
        h_sign_eq heq_guard hok
    exact hresult_ne h0
  · obtain ⟨M, ze', δ, zn, sticky, _, _, _, _, _, _, _, hok128, _, _, _⟩ :=
      operator_add_algorithmic_facts_diff_sign_represents x y result .to_nearest hx hy
        hx_mant_ne hy_mant_ne h_sign_eq heq_guard hok
    exact doNormalize128_zero_shape zn M ze' sticky .to_nearest result hok128 h0

/-- A mantissa-`0` `to_nearest` subtraction result of normalized operands is the
literal `Number.zero`. -/
lemma Number.operator_sub_zero_shape (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  unfold Number.operator_sub at hok
  exact Number.operator_add_zero_shape x y.operator_neg result hx
    (Number.operator_neg_isNormalized y hy) hok h0

/-- **Unconditional add normalization (`to_nearest`).** -/
lemma operator_add_isNormalized_to_nearest' (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · rw [Number.operator_add_zero_shape x y result hx hy hok h0]
    exact Or.inl rfl
  · exact operator_add_isNormalized_to_nearest x y result hx hy hok h0

/-- **Unconditional sub normalization (`to_nearest`).** -/
lemma operator_sub_isNormalized_to_nearest' (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result) :
    result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · rw [Number.operator_sub_zero_shape x y result hx hy hok h0]
    exact Or.inl rfl
  · exact operator_sub_isNormalized_to_nearest x y result hx hy hok h0

/-! ## STAmount canonical-shape exactness

The `ExactCanonical` shape and its `toNumber` exactness lemmas
(`toNumber_integral_small_exact`, `toNumber_exact_canonical`) live upstream in
`STAmountToNumber`; this section adds the integral-magnitude facts on top. -/

/-- On a non-negative canonical integral amount the stored magnitude is the
value. -/
lemma STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg (s : STAmount)
    (hc : s.IntegralCanonical) (hnn : 0 ≤ s.toRat) :
    ((s.mValue.toNat : ℕ) : ℚ) = s.toRat := by
  by_cases h : s.mIsNegative = true
  · have hm0 : s.mValue.toNat = 0 := by
      rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc] at hnn
      unfold STAmount.signedDrops at hnn
      rw [if_pos h] at hnn
      have h1 : (0 : ℤ) ≤ -(s.mValue.toNat : ℤ) := by exact_mod_cast hnn
      omega
    rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]
    unfold STAmount.signedDrops
    rw [if_pos h, hm0]
    norm_num
  · rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]
    unfold STAmount.signedDrops
    rw [if_neg h]
    norm_cast

/-- A canonical integral amount that is not `isZero` has nonzero value. -/
lemma STAmount.IntegralCanonical.toRat_ne_zero_of_not_isZero (s : STAmount)
    (hc : s.IntegralCanonical) (h : s.isZero = false) : s.toRat ≠ 0 := by
  have hm : s.mValue ≠ 0 := by
    intro h0
    rw [STAmount.isZero, h0] at h
    simp at h
  have hmN : s.mValue.toNat ≠ 0 := by
    intro h0
    exact hm (by exact_mod_cast UInt64.toNat_inj.mp (by rw [h0]; rfl))
  rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]
  unfold STAmount.signedDrops
  split
  · intro h0
    have : -(s.mValue.toNat : ℤ) = 0 := by exact_mod_cast h0
    omega
  · intro h0
    have : (s.mValue.toNat : ℤ) = 0 := by exact_mod_cast h0
    omega

/-- **`ofNumber .int64` record shape** on a non-negative integer-valued
normalized `Number` within `Int64`: the stored record is offset-`0`,
positive-signed, `.int64`-typed, and value-exact. -/
lemma STAmount.ofNumber_int64_shape (n : Number) (mode : rounding_mode) (sta : STAmount)
    (hn : n.isNormalized) (hnn : 0 ≤ n.toRat) (hden : n.toRat.den = 1)
    (hfit : n.toRat ≤ 2 ^ 63 - 1)
    (hok : STAmount.ofNumber .int64 n mode = .ok sta) :
    sta.mNumericType = .int64 ∧ sta.mOffset = 0 ∧ sta.mIsNegative = false ∧
      ((sta.mValue.toNat : ℕ) : ℚ) = n.toRat ∧ sta.toRat = n.toRat := by
  have hnegf : n.negative_ = false := Number.negative_false_of_normalized_nonneg n hn hnn
  have hsig : decide (n.signum < 0) = false := by
    unfold Number.signum
    rw [hnegf]
    simp only [Bool.false_eq_true, if_false]
    by_cases hm : (n.mantissa_ != 0) = true
    · rw [if_pos hm]; decide
    · rw [if_neg hm]; decide
  unfold STAmount.ofNumber at hok
  rw [hsig] at hok
  simp only [Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true] at hok
  cases hrep : n.to_rep mode with
  | error e => rw [hrep] at hok; simp at hok
  | ok rv =>
    rw [hrep] at hok
    simp only [] at hok
    have hexact : (rv.toInt : ℚ) = n.toRat :=
      int_cast_eq_of_abs_lt_one rv.toInt n.toRat hden (to_rep_within_one n mode rv hn hrep)
    have h0 : 0 ≤ rv.toInt := by
      have : (0 : ℚ) ≤ (rv.toInt : ℚ) := by rw [hexact]; exact hnn
      exact_mod_cast this
    have hhi : rv.toInt ≤ 2 ^ 63 - 1 := by
      have : (rv.toInt : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by
        rw [hexact]; exact le_trans hfit (by norm_num)
      exact_mod_cast this
    have hu64 : (rv.toUInt64.toNat : ℤ) = rv.toInt := toUInt64_toNat_of_nonneg rv h0
    unfold STAmount.checked STAmount.canonicalize at hok
    rw [if_pos (show (STAmount.unchecked .int64 rv.toUInt64 0 false).integral = true
      from rfl)] at hok
    by_cases hz : (rv.toUInt64 == 0) = true
    · rw [if_pos (show ((STAmount.unchecked .int64 rv.toUInt64 0 false).mValue == 0 ||
          decide ((STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset ≤ -20)) = true
          from by rw [show (STAmount.unchecked .int64 rv.toUInt64 0 false).mValue
            = rv.toUInt64 from rfl, hz]; rfl)] at hok
      have hsta : sta = { STAmount.unchecked .int64 rv.toUInt64 0 false with
          mValue := 0, mOffset := 0, mIsNegative := false } := (Except.ok.inj hok).symm
      have hval0 : n.toRat = 0 := by
        rw [← hexact, ← hu64, show rv.toUInt64 = 0 from by exact_mod_cast beq_iff_eq.mp hz]
        rfl
      subst hsta
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · rw [hval0]; rfl
      · rw [hval0]
        exact STAmount.toRat_zero_aux _ rfl rfl
    · rw [if_neg (show ¬ ((STAmount.unchecked .int64 rv.toUInt64 0 false).mValue == 0 ||
          decide ((STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset ≤ -20)) = true
          from by
        rw [show (STAmount.unchecked .int64 rv.toUInt64 0 false).mValue = rv.toUInt64 from rfl,
          show (STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset = (0 : Int) from rfl]
        rw [Bool.or_eq_true, not_or]
        exact ⟨by simpa using hz, by decide⟩)] at hok
      rw [if_neg (show ¬ (STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset >
          (STAmount.unchecked .int64 rv.toUInt64 0 false).mNumericType.maxOffset
          from by show ¬ ((0 : Int) > (18 : Int)); decide)] at hok
      simp only [IntAmount.ofNumber] at hok
      cases hr2 : (Number.unchecked (STAmount.unchecked .int64 rv.toUInt64 0 false).mIsNegative
          (STAmount.unchecked .int64 rv.toUInt64 0 false).mValue
          (STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset).to_rep mode with
      | error e => rw [hr2] at hok; simp at hok
      | ok r2 =>
        rw [hr2] at hok
        simp only [] at hok
        have hmaxrep : rv.toUInt64.toNat ≤ maxRep.toNat := by
          rw [maxRep_val]; omega
        have hkey := to_rep_exact_of_exponent_zero false rv.toUInt64 mode r2 hmaxrep hr2
        rw [if_neg (by exact Bool.false_ne_true)] at hkey
        have hr2v : r2.toInt = (rv.toUInt64.toNat : ℤ) := by
          have : (r2.toInt : ℚ) = ((rv.toUInt64.toNat : ℤ) : ℚ) := by
            rw [hkey]; push_cast; ring
          exact_mod_cast this
        have hna : r2.toInt.natAbs = rv.toUInt64.toNat := by omega
        have hvNat : r2.toInt.natAbs.toUInt64.toNat = r2.toInt.natAbs := by
          have hlt : r2.toInt.natAbs < 2 ^ 64 := by
            have := UInt64.toNat_lt_size rv.toUInt64
            omega
          exact UInt64.toNat_ofNat_of_lt hlt

        rw [if_neg (show ¬ (r2.toInt.natAbs.toUInt64 >
            (STAmount.unchecked .int64 rv.toUInt64 0 false).mNumericType.maxValue)
            from by
          show ¬ ((9223372036854775807 : UInt64) < r2.toInt.natAbs.toUInt64)
          rw [UInt64.lt_iff_toNat_lt, hvNat, hna,
            show (9223372036854775807 : UInt64).toNat = 9223372036854775807 from by decide]
          omega)] at hok

        have hnegr2 : decide (r2 < 0) = false := by
          rw [decide_eq_false_iff_not]
          intro hlt
          have h1 : r2.toInt < (0 : Int64).toInt := Int64.lt_iff_toInt_lt.mp hlt
          have h2 : (0 : Int64).toInt = 0 := by decide
          rw [h2, hr2v] at h1
          omega
        have hsta : sta = { mNumericType := NumericType.int64,
                            mValue := r2.toInt.natAbs.toUInt64, mOffset := 0,
                            mIsNegative := decide (r2 < 0) } :=
          (Except.ok.inj hok).symm
        subst hsta
        refine ⟨rfl, rfl, hnegr2, ?_, ?_⟩
        · show ((r2.toInt.natAbs.toUInt64.toNat : ℕ) : ℚ) = n.toRat
          rw [hvNat, hna, ← hexact, ← hu64]
          norm_cast
        · rw [STAmount.toRat_of_offset_zero _ rfl]
          unfold STAmount.signedDrops
          rw [show ({ mNumericType := NumericType.int64,
                      mValue := r2.toInt.natAbs.toUInt64, mOffset := 0,
                      mIsNegative := decide (r2 < 0) } : STAmount).mIsNegative
            = decide (r2 < 0) from rfl, hnegr2]
          simp only [Bool.false_eq_true, if_false]
          show ((r2.toInt.natAbs.toUInt64.toNat : ℤ) : ℚ) = n.toRat
          rw [hvNat, hna, ← hexact, ← hu64]

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Asset parity (`assetsAvailable = assetsTotal`) preservation -/

/-- A deposit preserves record-level asset parity: both asset fields receive
the identical `operator_add` update. -/
theorem Vault.deposit_asset_parity (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.vault'.assetsAvailable = r.vault'.assetsTotal := by
  unfold Vault.deposit at hok
  simp only [] at hok
  obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact hAV
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact hAV
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact hAV
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · rw [if_neg (by simp [hd])] at hok
          obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n3, hn3, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
          rw [hAV, hat] at hav
          have hae : av' = at' := (Except.ok.inj hav).symm
          by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
          · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact hAV
          · rw [if_neg hm] at hok
            obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h, (RawVault.to_lawful_ok htl).1]; exact hae
        · rw [if_pos (by simpa using hd)] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          cases cres with
          | error e => injection hok with h; rw [← h]; exact hAV
          | success rawAsset shares =>
            obtain ⟨assetDeposited, hclamp, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨precision, hprecision, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hp : precision = true
            · rw [if_pos hp] at hok; injection hok with h; rw [← h]; exact hAV
            · rw [if_neg hp] at hok
              obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨n3, hn3, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
              rw [hAV, hat] at hav
              have hae : av' = at' := (Except.ok.inj hav).symm
              by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
              · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact hAV
              · rw [if_neg hm] at hok
                obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
                injection hok with h; rw [← h, (RawVault.to_lawful_ok htl).1]; exact hae

/-- A withdrawal preserves record-level asset parity. -/
theorem Vault.withdraw_asset_parity (v : Vault) (amount : WithdrawAmount)
    (waive : Bool) (r : WithdrawResult)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hok : v.withdraw amount waive = .ok r) :
    r.vault'.assetsAvailable = r.vault'.assetsTotal := by
  unfold Vault.withdraw at hok
  simp only [] at hok
  cases amount
  all_goals {
    simp only [] at hok
    obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h1 : result.error.isSome = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact hAV
    · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
      obtain ⟨aN, haN, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h2 : v.assetsAvailable.operator_lt aN = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact hAV
      · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
        obtain ⟨sta, hsta, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h3 : result.sharesRedeemed.operator_eq sta = true
        · rw [if_pos h3] at hok
          by_cases h4 : v.lossUnrealized.operator_ne Number.zero = true
          · rw [if_pos h4] at hok; injection hok with h; rw [← h]; exact hAV
          · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
            obtain ⟨allAvail, hall, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h, (RawVault.to_lawful_ok htl).1]
        · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
          obtain ⟨assetDebited, hclamp, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨precision, hprecision, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases h4 : precision = true
          · rw [if_pos h4] at hok; injection hok with h; rw [← h]; exact hAV
          · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
            obtain ⟨finalAssetNumber, hfinal, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨sN, hsN, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨atr, hatr, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨atr', hatr', hok⟩ := bind_ok_peel _ _ _ hok
            by_cases h5 : (finalAssetNumber.mantissa_ != 0 && atr.operator_eq atr') = true
            · rw [if_pos h5] at hok; injection hok with h; rw [← h]; exact hAV
            · rw [if_neg h5] at hok; try simp only [pure_bind] at hok
              obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
              rw [hAV, hat] at hav
              have hae : av' = at' := (Except.ok.inj hav).symm
              injection hok with h; rw [← h, (RawVault.to_lawful_ok htl).1]; exact hae
  }

/-- A clawback preserves record-level asset parity. -/
theorem Vault.clawback_asset_parity (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hok : v.clawback assets holderShares = .ok r) :
    r.vault'.assetsAvailable = r.vault'.assetsTotal := by
  unfold Vault.clawback at hok
  simp only [] at hok
  obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : result.error.isSome = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact hAV
  · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
    by_cases h2 : result.sharesDestroyed.isZero = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact hAV
    · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
      obtain ⟨sdn, hsdn, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨arn, harn, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr, hatr, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr', hatr', hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h3 : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact hAV
      · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
        obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
        rw [hAV, hat] at hav
        have hae : av' = at' := (Except.ok.inj hav).symm
        injection hok with h; rw [← h, (RawVault.to_lawful_ok htl).1]; exact hae

/-- A share burn preserves record-level asset parity: it writes only
`sharesTotal`. -/
theorem Vault.burnShares_asset_parity (v : Vault) (sharesDestroyed : STAmount)
    (v' : Vault) (hAV : v.assetsAvailable = v.assetsTotal)
    (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.assetsAvailable = v'.assetsTotal := by
  unfold Vault.burnShares at hok
  simp only [] at hok
  obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
  rw [(RawVault.to_lawful_ok hok).1]; exact hAV

end XRPL.Model.SingleAssetVault
