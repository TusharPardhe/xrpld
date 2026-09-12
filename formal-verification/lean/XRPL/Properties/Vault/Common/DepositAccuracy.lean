import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.NumberBridge
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Vault.Common.DepositExits
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Protocol.Number.Add.RoundsWithin
import XRPL.Properties.Protocol.Number.Sub.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Normalize.RoundsWithin
import XRPL.Properties.Protocol.Number.Normalize.RoundsToRepresentable

/-! # `Vault.deposit` accuracy proofs

Proof bodies behind the accuracy headlines in `VaultDeposit.lean`. -/

namespace XRPL.Model.Protocol

/-! ## Generic `STAmount` grid facts -/

/-- Signed-integer-times-grid-step form of `STAmount.toRat`. -/
lemma STAmount.exists_int_grid (a : STAmount) :
    ∃ z : ℤ, a.toRat = (z : ℚ) * 10 ^ a.exponent := by
  refine ⟨if a.mIsNegative then -(a.mValue.toNat : ℤ) else (a.mValue.toNat : ℤ), ?_⟩
  rw [STAmount.toRat_signed]
  show _ = _ * (10 : ℚ) ^ a.mOffset
  rcases h : a.mIsNegative with _ | _ <;> simp

/-- Any `STAmount` sits on its own exponent grid: the trivial `.downward` floor
equation at `s = a.exponent`. -/
lemma STAmount.self_grid (a : STAmount) :
    RoundsToRepresentableAt a a.toRat a.exponent .downward := by
  show a.toRat = (⌊a.toRat / 10 ^ a.exponent⌋ : ℚ) * 10 ^ a.exponent
  obtain ⟨z, hval⟩ := STAmount.exists_int_grid a
  have h10 : ((10 : ℚ) ^ a.exponent) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hdiv : a.toRat / 10 ^ a.exponent = (z : ℚ) := by
    rw [hval]; field_simp
  rw [hdiv, Int.floor_intCast, ← hval]

/-- A nonzero `STAmount` is at least one step of its own grid. -/
lemma STAmount.ulp_le_abs_toRat (a : STAmount) (h : a.mValue ≠ 0) :
    (10 : ℚ) ^ a.exponent ≤ |a.toRat| := by
  rw [STAmount.abs_toRat]
  show (10 : ℚ) ^ a.mOffset ≤ _
  have hnat : a.mValue.toNat ≠ 0 := by
    intro h0
    exact h (by rw [← UInt64.toNat_inj] at *; exact h0)
  have h1 : (1 : ℚ) ≤ (a.mValue.toNat : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnat
  nlinarith [zpow_pos (show (0 : ℚ) < 10 by norm_num) a.mOffset]

/-- A nonzero-mantissa `STAmount` has nonzero value. -/
lemma STAmount.toRat_ne_zero (a : STAmount) (h : a.mValue ≠ 0) : a.toRat ≠ 0 := by
  intro h0
  have hle := STAmount.ulp_le_abs_toRat a h
  rw [h0, abs_zero] at hle
  exact absurd hle (not_le.mpr (zpow_pos (by norm_num) _))

/-! ## Canonical-offset range of the fractional pipeline -/

/-- `IOUAmount.ofMantissaExp` output exponent: the canonical zero (`-100`) or the
clamped IOU range `[-96, 80]`. -/
lemma IOUAmount.ofMantissaExp_exponent_cases (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hok : IOUAmount.ofMantissaExp m e mode = .ok i) :
    i.exponent_ = -100 ∨ ((-96 : ℤ) ≤ i.exponent_ ∧ i.exponent_ ≤ 80) := by
  unfold IOUAmount.ofMantissaExp IOUAmount.normalize at hok
  by_cases hm : (m == 0) = true
  · rw [if_pos hm] at hok
    rw [← Except.ok.inj hok]
    exact Or.inl rfl
  · rw [if_neg hm] at hok
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error e' => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e' => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        · rw [if_neg hhi] at hok
          by_cases hlo : r.exponent_ < cMinOffset
          · rw [if_pos hlo] at hok
            rw [← Except.ok.inj hok]
            exact Or.inl rfl
          · rw [if_neg hlo] at hok
            rw [← Except.ok.inj hok]
            right
            have h1 := not_lt.mp hlo
            have h2 := not_lt.mp hhi
            unfold cMinOffset at h1
            unfold cMaxOffset at h2
            omega

/-- `STAmount.canonicalize` on a fractional record: the output offset is the
canonical zero offset (`-100`) or within the clamped IOU range `[-96, 80]`. -/
lemma STAmount.canonicalize_fractional_offset (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional)
    (hok : s.canonicalize mode = .ok result) :
    result.mOffset = -100 ∨ ((-96 : ℤ) ≤ result.mOffset ∧ result.mOffset ≤ 80) := by
  have hint : ¬ s.integral = true := by
    unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
    unfold STAmount.iou; rw [if_neg hint]
  rw [hiou] at hok
  cases hone : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode with
  | error e => rw [hone] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hone] at hok
    simp only [] at hok
    have heq := Except.ok.inj hok
    have hres : result.mOffset = i.exponent_ := by rw [← heq]
    rw [hres]
    exact IOUAmount.ofMantissaExp_exponent_cases _ _ mode i hone

/-- `STAmount.ofNumber` on a fractional asset: the output offset is `-100` (zero)
or within `[-96, 80]`. -/
lemma STAmount.ofNumber_fractional_offset (nt : NumericType) (n : Number) (mode : rounding_mode)
    (a : STAmount) (hnt : nt = .fractional)
    (hok : STAmount.ofNumber nt n mode = .ok a) :
    a.mOffset = -100 ∨ ((-96 : ℤ) ≤ a.mOffset ∧ a.mOffset ≤ 80) := by
  subst hnt
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ NumericType.fractional.isIntegral = true)] at hok
  cases hnr : (if decide (n.signum < 0) = true then n.operator_neg else n).normalizeToRange
      kMinValue kMaxValue mode with
  | error e => rw [hnr] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨m', e'⟩ := me
    rw [hnr] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    exact STAmount.canonicalize_fractional_offset _ a mode rfl hok

/-! ## Integral (`int64`/`native`) canonicality and exactness of the packing -/

/-- The `ofNumber` sign flag is just the operand's sign bit. -/
lemma Number.signum_neg_decide (n : Number) : decide (n.signum < 0) = n.negative_ := by
  unfold Number.signum
  rcases h : n.negative_ with _ | _
  · by_cases hm : (n.mantissa_ != 0) = true <;> simp [hm]
  · simp

/-- `STAmount.canonicalize` on an integral offset-`0` record: the result is a
canonical integral record of the same numeric type. -/
lemma STAmount.canonicalize_integral_canonical (s result : STAmount) (mode : rounding_mode)
    (hint : s.integral = true)
    (hok : s.canonicalize mode = .ok result) :
    result.IntegralCanonical ∧ result.mNumericType = s.mNumericType := by
  rw [STAmount.canonicalize, if_pos hint] at hok
  by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
  · rw [if_pos hz] at hok
    rw [← Except.ok.inj hok]
    exact ⟨⟨hint, rfl, by simp⟩, rfl⟩
  · rw [if_neg hz] at hok
    by_cases hmoff : s.mOffset > s.mNumericType.maxOffset
    · rw [if_pos hmoff] at hok; exact absurd hok (by simp)
    rw [if_neg hmoff] at hok
    simp only [IntAmount.ofNumber] at hok
    cases hr : (Number.unchecked s.mIsNegative s.mValue s.mOffset).to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only [] at hok
      by_cases hrng : r.toInt.natAbs.toUInt64 > s.mNumericType.maxValue
      · rw [if_pos hrng] at hok; exact absurd hok (by simp)
      rw [if_neg hrng] at hok
      rw [← Except.ok.inj hok]
      refine ⟨⟨hint, rfl, ?_⟩, rfl⟩
      show r.toInt.natAbs.toUInt64.toNat ≤ s.mNumericType.maxValue.toNat
      by_contra hcon
      exact hrng (UInt64.lt_iff_toNat_lt.mpr (by omega))

/-- `STAmount.ofNumber` on an integral type: the result is a canonical integral
record of that type. -/
lemma STAmount.ofNumber_integral_canonical (nt : NumericType) (n : Number)
    (mode : rounding_mode) (a : STAmount)
    (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok a) :
    a.IntegralCanonical ∧ a.mNumericType = nt := by
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  cases hrep : (if decide (n.signum < 0) = true then n.operator_neg else n).to_rep mode with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    exact STAmount.canonicalize_integral_canonical _ a mode
      (show (STAmount.unchecked nt intValue.toUInt64 0 (decide (n.signum < 0))).integral = true
        from hnt) hok

/-- The `Number.mantissa` accessor of a zero-mantissa record is zero. -/
lemma Number.mantissa_acc_zero {n : Number} (h : n.mantissa_ = 0) : n.mantissa = 0 := by
  unfold Number.mantissa
  rw [h, if_neg (by decide : ¬ ((0 : UInt64) > maxRep))]
  split <;> decide

/-- A nonzero integral `ofNumber` result forces a nonzero source mantissa. -/
lemma STAmount.ofNumber_integral_source_ne_zero (nt : NumericType) (n : Number)
    (mode : rounding_mode) (a : STAmount)
    (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok a) (ha : a.mValue ≠ 0) :
    n.mantissa_ ≠ 0 := by
  intro h0
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  have hwm : w.mantissa_ = 0 := by
    rw [hw]
    split
    · unfold Number.operator_neg
      rw [if_pos (by rw [h0]; rfl)]
      rfl
    · exact h0
  have hrep : w.to_rep mode = .ok 0 := by
    unfold Number.to_rep
    rw [if_pos (show (w.mantissa == 0) = true from by
      rw [Number.mantissa_acc_zero hwm]; decide)]
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt, ← hw, hrep] at hok
  simp only [] at hok
  rw [show ((0 : rep).toUInt64) = (0 : UInt64) from by decide] at hok
  rw [STAmount.checked, STAmount.canonicalize,
    if_pos (show (STAmount.unchecked nt 0 0 (decide (n.signum < 0))).integral = true from hnt),
    if_pos (show ((STAmount.unchecked nt 0 0 (decide (n.signum < 0))).mValue == 0
      || decide ((STAmount.unchecked nt 0 0 (decide (n.signum < 0))).mOffset ≤ -20)) = true
      from rfl)] at hok
  apply ha
  rw [← Except.ok.inj hok]

/-- A nonzero truncation forces a nonzero input mantissa. -/
lemma Number.truncate_source_ne_zero (n t : Number)
    (hok : n.truncate = .ok t) (ht : t.mantissa_ ≠ 0) : n.mantissa_ ≠ 0 := by
  intro h0
  unfold Number.truncate at hok
  rw [if_pos (Or.inr h0)] at hok
  rw [← Except.ok.inj hok] at ht
  exact ht h0

/-- `STAmount.ofNumber` on an integral type is value-exact for a normalized
integer-valued `Number` (`den = 1`). -/
lemma STAmount.ofNumber_integral_exact (nt : NumericType) (n : Number)
    (mode : rounding_mode) (a : STAmount)
    (hnt : nt.isIntegral = true)
    (hn : n.isNormalized) (hden : n.toRat.den = 1)
    (hok : STAmount.ofNumber nt n mode = .ok a) :
    a.toRat = n.toRat := by
  by_cases hm : n.mantissa_ = 0
  · -- zero source, zero result
    have hn0 : n.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero n hm
    have ha0 : a.mValue = 0 := by
      by_contra hc
      exact STAmount.ofNumber_integral_source_ne_zero nt n mode a hnt hok hc hm
    rw [hn0, STAmount.toRat_signed, ha0]
    simp
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  have hwn : w = if n.negative_ = true then n.operator_neg else n := by
    rw [hw, Number.signum_neg_decide]
  have hw_norm : w.isNormalized := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]; exact hn
    · rw [if_pos rfl]; exact Number.operator_neg_isNormalized n hn
  have hneg_rec : n.operator_neg = { n with negative_ := !n.negative_ } := by
    unfold Number.operator_neg
    rw [if_neg (by simpa using hm)]
  have hw_exp : w.exponent_ = n.exponent_ := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]
    · rw [if_pos rfl, hneg_rec]
  have hw_neg : w.negative_ = false := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]; exact hb
    · rw [if_pos rfl, hneg_rec]
      simp [hb]
  have hw_val : w.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) * n.toRat := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      ring
    · rw [if_pos rfl, if_pos rfl, Number.toRat_neg]; ring
  cases hrep : w.to_rep mode with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    have hwden : w.toRat.den = 1 := by
      rw [hw_val]
      rcases hb : n.negative_ with _ | _
      · simpa using hden
      · rw [if_pos rfl, neg_one_mul, Rat.neg_den]
        exact hden
    have hkey : (intValue.toInt : ℚ) = w.toRat := by
      have hone := to_rep_within_one w mode intValue hw_norm hrep
      have hwq : w.toRat = (w.toRat.num : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den w.toRat]
        rw [hwden]; simp
      rw [hwq] at hone ⊢
      have habs : |intValue.toInt - w.toRat.num| < 1 := by
        rw [← Int.cast_sub, ← Int.cast_abs] at hone
        exact_mod_cast hone
      have heq : intValue.toInt = w.toRat.num := by
        have := abs_lt.mp habs
        omega
      rw [heq]
    have hw_nonneg : 0 ≤ w.toRat := by
      rw [Number.toRat_of_nonneg w hw_neg]; positivity
    have hiv_nonneg : (0 : ℤ) ≤ intValue.toInt := by
      have : (0 : ℚ) ≤ (intValue.toInt : ℚ) := by rw [hkey]; exact hw_nonneg
      exact_mod_cast this
    have hiv_le : intValue.toInt ≤ (2 : ℤ) ^ 63 - 1 := by
      have := Int64.toInt_lt intValue
      omega
    have htu : (intValue.toUInt64.toNat : ℤ) = intValue.toInt :=
      toUInt64_toNat_of_nonneg intValue hiv_nonneg
    have hfit : intValue.toUInt64.toNat ≤ maxRep.toNat := by
      rw [maxRep_val]
      omega
    have hexact := STAmount.canonicalize_integral_toRat _ a mode
      (show (STAmount.unchecked nt intValue.toUInt64 0 (decide (n.signum < 0))).integral = true
        from hnt) rfl hfit hok
    rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
    show ((if decide (n.signum < 0) = true then -(intValue.toUInt64.toNat : ℤ)
      else (intValue.toUInt64.toNat : ℤ) : ℤ) : ℚ) = n.toRat
    rw [Number.signum_neg_decide]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]
      have : ((intValue.toUInt64.toNat : ℤ) : ℚ) = n.toRat := by
        rw [htu, hkey, hw_val, hb]; simp
      exact_mod_cast this
    · rw [if_pos rfl]
      have h1 : ((intValue.toUInt64.toNat : ℤ) : ℚ) = -n.toRat := by
        rw [htu, hkey, hw_val, hb]; simp
      push_cast
      push_cast at h1
      linarith

/-- The value of a canonical integral amount is bounded by its type's carried
maximum. -/
lemma STAmount.IntegralCanonical.abs_toRat_le (s : STAmount) (hc : s.IntegralCanonical) :
    |s.toRat| ≤ (s.mNumericType.maxValue.toNat : ℚ) := by
  rw [STAmount.abs_toRat, hc.offset_zero]
  have := hc.in_range
  simp only [zpow_zero, mul_one]
  exact_mod_cast this

/-- The sum of two integer-valued rationals is integer-valued. -/
lemma Rat.den_one_add (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) : (a + b).den = 1 := by
  have haq : a = (a.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den a]
    rw [ha]; simp
  have hbq : b = (b.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den b]
    rw [hb]; simp
  rw [haq, hbq, ← Int.cast_add]
  exact Rat.den_intCast _

/-- Numerator magnitude bound of an integer-valued rational. -/
lemma Rat.num_natAbs_lt_of_abs_le (q : ℚ) (hden : q.den = 1)
    (h : |q| ≤ (2 : ℚ) ^ 63 - 1) : q.num.natAbs < 2 ^ 63 := by
  have hq : q = (q.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    rw [hden]; simp
  have habs : |(q.num : ℚ)| ≤ (2 : ℚ) ^ 63 - 1 := by rw [← hq]; exact h
  have : (|q.num| : ℚ) ≤ (2 : ℚ) ^ 63 - 1 := by exact_mod_cast habs
  have hle : |q.num| ≤ (2 : ℤ) ^ 63 - 1 := by exact_mod_cast this
  rw [Int.abs_eq_natAbs] at hle
  omega

/-- `to_nearest` `Number` addition of two non-negative normalized operands rounds
within the keystone relative error, with the zero cases exact. -/
lemma operator_add_nonneg_rounds (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    RoundsWithin result (x.toRat + y.toRat) .to_nearest (6 / (2 ^ 63 - 3 : ℚ)) := by
  have hε : (0 : ℚ) ≤ 6 / (2 ^ 63 - 3 : ℚ) := by positivity
  by_cases hym : y.mantissa_ = 0
  · have hy0 : y = Number.zero := Number.eq_zero_of_mantissa_zero y hy hym
    have hres : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos (by rw [hy0]; decide)] at hok
      exact (Except.ok.inj hok).symm
    refine RoundsWithin_mono result _ 0 _ _ (RoundsWithin_of_eq result _ _ ?_) hε
    rw [hres, hy0, Number.toRat_zero, add_zero]
    rfl
  by_cases hxm : x.mantissa_ = 0
  · have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx hxm
    have hres : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hym),
          if_pos (by rw [hx0]; decide)] at hok
      exact (Except.ok.inj hok).symm
    refine RoundsWithin_mono result _ 0 _ _ (RoundsWithin_of_eq result _ _ ?_) hε
    rw [hres, hx0, Number.toRat_zero, zero_add]
    rfl
  -- both nonzero: same-sign (non-negative) addition
  have hxneg : x.negative_ = false := by
    rcases hb : x.negative_ with _ | _
    · rfl
    · exfalso
      have := Number.toRat_of_neg x hb
      have hxpos : (0 : ℚ) < (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ := by
        have h1 : x.mantissa_.toNat ≠ 0 := by
          intro h0; exact hxm (by rw [← UInt64.toNat_inj] at *; exact h0)
        have h2 : (1 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
        positivity
      rw [this] at hxnn
      linarith
  have hyneg : y.negative_ = false := by
    rcases hb : y.negative_ with _ | _
    · rfl
    · exfalso
      have := Number.toRat_of_neg y hb
      have hypos : (0 : ℚ) < (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_ := by
        have h1 : y.mantissa_.toNat ≠ 0 := by
          intro h0; exact hym (by rw [← UInt64.toNat_inj] at *; exact h0)
        have h2 : (1 : ℚ) ≤ (y.mantissa_.toNat : ℚ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
        positivity
      rw [this] at hynn
      linarith
  have hnotz : ¬ x.operator_eq y.operator_neg = true := by
    intro hcon
    have hnegy : y.operator_neg = { y with negative_ := !y.negative_ } := by
      unfold Number.operator_neg
      rw [if_neg (by simpa using hym)]
    unfold Number.operator_eq at hcon
    rw [hnegy] at hcon
    simp only [Bool.and_eq_true, beq_iff_eq] at hcon
    have := hcon.1.1
    rw [hxneg, hyneg] at this
    exact Bool.noConfusion this
  have h := operator_add_rounds_same_sign_to_nearest x y result hx hy hxm hym
    (by rw [hxneg, hyneg]) hnotz hok
  refine RoundsWithin_mono result _ _ _ _ h (by norm_num)

/-! ## `Number.truncate` computes the floor of a non-negative value -/

/-- Rational floor of a natural division. -/
lemma Int.floor_nat_div (a b : ℕ) (hb : 0 < b) :
    ⌊(a : ℚ) / (b : ℚ)⌋ = ((a / b : ℕ) : ℤ) := by
  have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hbq]
    exact_mod_cast Nat.div_mul_le_self a b
  · rw [div_lt_iff₀ hbq]
    have hlt : a < (a / b + 1) * b := by
      have hdm := Nat.div_add_mod a b
      have hmod := Nat.mod_lt a hb
      calc a = b * (a / b) + a % b := hdm.symm
        _ < b * (a / b) + b := by omega
        _ = (a / b + 1) * b := by ring
    exact_mod_cast hlt

/-- `truncateAux` divides out the negative exponent: the resulting value is the
natural quotient by `10 ^ (-e)`, the mantissa never grows, and a nonzero result
lands at exponent `0`. -/
lemma Number.truncateAux_val (m : UInt64) (e : Int) :
    e ≤ 0 →
    ((Number.truncateAux m e).1.toNat : ℚ) * 10 ^ (Number.truncateAux m e).2
        = ((m.toNat / 10 ^ (-e).toNat : ℕ) : ℚ) ∧
      (Number.truncateAux m e).1.toNat ≤ m.toNat ∧
      ((Number.truncateAux m e).1.toNat ≠ 0 → (Number.truncateAux m e).2 = 0) := by
  induction m, e using Number.truncateAux.induct with
  | case1 m e h ih =>
    intro he
    rw [show Number.truncateAux m e = Number.truncateAux (m / 10) (e + 1) from by
      rw [Number.truncateAux, if_pos h]]
    obtain ⟨hval, hle, hzero⟩ := ih (by omega)
    have hdiv10 : (m / 10).toNat = m.toNat / 10 := by
      rw [UInt64.toNat_div]
      rfl
    refine ⟨?_, ?_, hzero⟩
    · rw [hval]
      congr 1
      rw [hdiv10, Nat.div_div_eq_div_mul]
      congr 1
      have hd : (-e).toNat = (-(e + 1)).toNat + 1 := by omega
      rw [hd, pow_succ]
      ring
    · rw [hdiv10] at hle
      exact le_trans hle (Nat.div_le_self _ _)
  | case2 m e h =>
    intro he
    rw [show Number.truncateAux m e = (m, e) from by
      rw [Number.truncateAux, if_neg h]]
    by_cases he0 : e = 0
    · subst he0
      refine ⟨by norm_num, le_refl _, fun _ => rfl⟩
    · have hm : m = 0 := by
        rcases not_and_or.mp h with h1 | h2
        · omega
        · simpa using h2
      subst hm
      refine ⟨by norm_num, le_refl _, fun h0 => absurd rfl h0⟩

/-- **`Number.truncate` floors a non-negative normalized value.** The result is
the integer part, integer-valued, and normalized whenever nonzero. -/
lemma Number.truncate_floor (n t : Number) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hok : n.truncate = .ok t) :
    t.toRat = (⌊n.toRat⌋ : ℚ) ∧ (t.mantissa_ ≠ 0 → t.isNormalized) := by
  unfold Number.truncate at hok
  by_cases hg : n.exponent_ ≥ 0 ∨ n.mantissa_ = 0
  · rw [if_pos hg] at hok
    have ht : t = n := (Except.ok.inj hok).symm
    subst ht
    by_cases hm : t.mantissa_ = 0
    · have h0 : t.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero t hm
      rw [h0]
      norm_num
      exact fun h => absurd hm h
    · have hexp : 0 ≤ t.exponent_ := by
        rcases hg with h | h
        · exact h
        · exact absurd h hm
      have hval : t.toRat = ((t.mantissa_.toNat * 10 ^ t.exponent_.toNat : ℕ) : ℚ) := by
        rw [Number.toRat_of_nonneg t hneg]
        push_cast
        rw [← zpow_natCast (10 : ℚ) t.exponent_.toNat, Int.toNat_of_nonneg hexp]
      rw [hval, Int.floor_natCast]
      exact ⟨rfl, fun _ => hn⟩
  · rw [if_neg hg] at hok
    push_neg at hg
    obtain ⟨hexp_neg', hm_ne⟩ := hg
    have hexp_neg : n.exponent_ < 0 := by omega
    -- expose the truncated pair
    obtain ⟨hval, hle, hzero⟩ := Number.truncateAux_val n.mantissa_ n.exponent_ (le_of_lt hexp_neg)
    cases hp : Number.truncateAux n.mantissa_ n.exponent_ with
    | mk m' e' =>
      rw [hp] at hok hval hle hzero
      simp only [] at hok hval hle hzero
      -- the target integer value
      set K : ℕ := n.mantissa_.toNat / 10 ^ (-n.exponent_).toNat with hK
      -- the input to the final normalize denotes exactly `K`
      have hin_val : (Number.unchecked n.negative_ m' e').toRat = (K : ℚ) := by
        rw [Number.toRat_of_nonneg _
          (show (Number.unchecked n.negative_ m' e').negative_ = false from hneg)]
        exact hval
      -- `K` is the floor of the value
      have hfloor : ⌊n.toRat⌋ = (K : ℤ) := by
        have hd_pos : 0 < 10 ^ (-n.exponent_).toNat := by positivity
        have hnval : n.toRat = (n.mantissa_.toNat : ℚ) / ((10 ^ (-n.exponent_).toNat : ℕ) : ℚ) := by
          rw [Number.toRat_of_nonneg n hneg]
          push_cast
          rw [← zpow_natCast (10 : ℚ) (-n.exponent_).toNat,
            Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n.exponent_),
            zpow_neg, div_eq_mul_inv, inv_inv]
        rw [hnval, Int.floor_nat_div _ _ hd_pos]
      -- `K` is representable: at most 18 digits
      have hK_lt : K < 2 ^ 63 := by
        have hmb := hn.mantissaBounds hm_ne
        have hmax : n.mantissa_.toNat ≤ largeRange.max.toNat := UInt64.le_iff_toNat_le.mp hmb.2
        have hmaxv : largeRange.max.toNat = 9999999999999999999 := by decide
        have hd_ge : 10 ≤ 10 ^ (-n.exponent_).toNat := by
          have h1 : 1 ≤ (-n.exponent_).toNat := by omega
          calc (10 : ℕ) = 10 ^ 1 := by norm_num
            _ ≤ 10 ^ (-n.exponent_).toNat := Nat.pow_le_pow_right (by norm_num) h1
        have : K ≤ n.mantissa_.toNat / 10 := Nat.div_le_div_left hd_ge (by norm_num)
        have h10 : n.mantissa_.toNat / 10 ≤ 999999999999999999 := by omega
        omega
      -- the final normalize is exact on the representable target
      have hgrid := normalize_rounded_to_nearest (Number.unchecked n.negative_ m' e') t hok
      rw [hin_val] at hgrid
      have hrep : ∃ w : Number, w.isNormalized ∧ w.toRat = (K : ℚ) := by
        rcases Nat.eq_zero_or_pos K with h0 | hpos
        · exact ⟨Number.zero, Or.inl rfl, by rw [Number.toRat_zero, h0]; norm_num⟩
        · obtain ⟨w, hw1, _, hw3⟩ := Number.exists_normalized_of_pos_nat K hpos hK_lt
          exact ⟨w, hw1, hw3⟩
      obtain ⟨w, hw_norm, hw_val⟩ := hrep
      have hexact : t.toRat = (K : ℚ) :=
        Number.RoundsToRepresentable.eq_of_representable t _ hgrid w hw_norm hw_val
      refine ⟨by rw [hexact, hfloor]; norm_cast, ?_⟩
      intro ht_ne
      have hm' : m' ≠ 0 := by
        intro h0
        have hKzero : (K : ℚ) = 0 := by
          rw [← hval, h0]
          norm_num
        have := Number.toRat_ne_zero_of_mantissa_ne_zero t ht_ne
        rw [hexact] at this
        exact this hKzero
      exact normalize_result_isNormalized (Number.unchecked n.negative_ m' e') t .to_nearest
        (by simpa using hm') hok ht_ne

/-! ## Canonical `toNumber` exactness and magnitude floor -/

/-- `toNumber` is value-exact and normalized on any deposit-ready amount. -/
lemma STAmount.toNumber_canonical_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.Canonical) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized := by
  by_cases hint : s.integral = true
  · obtain ⟨hic, hmax⟩ := hc.1 hint
    obtain ⟨sn, h1, h2, h3, _⟩ := STAmount.toNumber_integral_exact s mode hic hmax
    exact ⟨sn, h1, h2, h3⟩
  · have hfr : s.integral = false := by
      rcases hb : s.integral with _ | _
      · rfl
      · exact absurd hb hint
    exact STAmount.toNumber_iou_exact s mode (hc.2 hfr)

/-- A nonzero deposit-ready amount is at least `10 ^ (-81)` in magnitude. -/
lemma STAmount.Canonical.abs_toRat_ge (s : STAmount) (hc : s.Canonical)
    (hnz : s.mValue ≠ 0) : (10 : ℚ) ^ (-81 : ℤ) ≤ |s.toRat| := by
  rw [STAmount.abs_toRat]
  by_cases hint : s.integral = true
  · obtain ⟨hic, _⟩ := hc.1 hint
    rw [hic.offset_zero]
    have h1 : 1 ≤ s.mValue.toNat := by
      have : s.mValue.toNat ≠ 0 := by
        intro h0
        exact hnz (by rw [← UInt64.toNat_inj] at *; exact h0)
      omega
    have h1q : (1 : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast h1
    have hp : ((10 : ℚ) ^ (-81 : ℤ)) ≤ 1 := by
      rw [show ((-81) : ℤ) = -(81 : ℕ) from rfl, zpow_neg, zpow_natCast]
      rw [inv_le_one_iff₀]
      right
      norm_num
    calc (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := hp
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ (0 : ℤ) := by norm_num; exact h1
  · have hfr : s.integral = false := by
      rcases hb : s.integral with _ | _
      · rfl
      · exact absurd hb hint
    have hio := hc.2 hfr
    have hm : (10 ^ 15 : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast hio.mant_lo
    have hoff : (10 : ℚ) ^ (-96 : ℤ) ≤ (10 : ℚ) ^ s.mOffset :=
      zpow_le_zpow_right₀ (by norm_num) hio.exp_lo
    have hsplit : (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 15, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
    rw [hsplit]
    have h10 : (0 : ℚ) < (10 : ℚ) ^ s.mOffset := zpow_pos (by norm_num) _
    calc (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ)
        ≤ (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ s.mOffset := by
          exact mul_le_mul_of_nonneg_left hoff (by positivity)
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ s.mOffset := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hio.mant_lo) (le_of_lt h10)

/-- A nonnegative nonzero deposit amount is strictly positive: it clears
the `10 ^ (-81)` magnitude floor, so it cannot be the zero rational. -/
lemma STAmount.Canonical.toRat_pos_of_nonneg (s : STAmount) (hc : s.Canonical)
    (hnn : 0 ≤ s.toRat) (hnz : s.isZero = false) : 0 < s.toRat := by
  have hfloor := STAmount.Canonical.abs_toRat_ge s hc (ne_of_beq_false hnz)
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso; rw [← h, abs_zero] at hfloor
    linarith [show (0 : ℚ) < 10 ^ (-81 : ℤ) from zpow_pos (by norm_num) _]

/-! ## Relative-error composition of the `mul`/`div` exchange pipeline -/

/-- Compose the three stage errors of `T0 / nav` computed as
`(T0·(1+δ₂)) / (nav·(1+δ₁))` then rounded once more: the result stays within
relative error `E` of `T0 / nav`, given the numeric closure conditions. -/
lemma div_pipeline_rel_bound (nav N T0 PP QQ ε₁ ε₂ ε₃ E : ℚ)
    (hT0 : 0 < T0) (hQQ : 0 ≤ QQ)
    (h1 : |N - nav| ≤ nav * ε₁)
    (h2 : |PP - T0| ≤ T0 * ε₂)
    (h3 : |QQ * N - PP| ≤ PP * ε₃)
    (hε₁ : 0 ≤ ε₁) (hε₁1 : ε₁ < 1)
    (hε₂1 : ε₂ < 1)
    (hε₃ : 0 ≤ ε₃) (hε₃1 : ε₃ ≤ 1)
    (hup : (1 + ε₂) * (1 + ε₃) ≤ (1 + E) * (1 - ε₁))
    (hlo : (1 - E) * (1 + ε₁) ≤ (1 - ε₂) * (1 - ε₃)) :
    |QQ * nav - T0| ≤ T0 * E := by
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  obtain ⟨h3l, h3r⟩ := abs_le.mp h3
  have hPP : 0 < PP := by nlinarith
  rw [abs_le]
  constructor
  · -- lower side: T0 * (1 - E) ≤ QQ * nav
    have key : T0 * ((1 - E) * (1 + ε₁)) ≤ QQ * nav * (1 + ε₁) := by
      have s1 : T0 * ((1 - E) * (1 + ε₁)) ≤ T0 * ((1 - ε₂) * (1 - ε₃)) := by nlinarith
      have s2 : T0 * ((1 - ε₂) * (1 - ε₃)) ≤ PP * (1 - ε₃) := by nlinarith
      have s3 : PP * (1 - ε₃) ≤ QQ * N := by nlinarith
      have s4 : QQ * N ≤ QQ * nav * (1 + ε₁) := by nlinarith
      linarith
    have hpos : (0 : ℚ) < 1 + ε₁ := by linarith
    nlinarith [key]
  · -- upper side: QQ * nav ≤ T0 * (1 + E)
    have key : QQ * nav * (1 - ε₁) ≤ T0 * ((1 + E) * (1 - ε₁)) := by
      have s1 : QQ * nav * (1 - ε₁) ≤ QQ * N := by nlinarith
      have s2 : QQ * N ≤ PP * (1 + ε₃) := by nlinarith
      have s3 : PP * (1 + ε₃) ≤ T0 * ((1 + ε₂) * (1 + ε₃)) := by nlinarith
      have s4 : T0 * ((1 + ε₂) * (1 + ε₃)) ≤ T0 * ((1 + E) * (1 - ε₁)) := by nlinarith
      linarith
    have hpos : (0 : ℚ) < 1 - ε₁ := by linarith
    nlinarith [key]

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- When the exchange rate still equals `10 ^ scale`, `idealSharesDeposit` is the
empty-vault formula. -/
theorem Vault.idealSharesDeposit_initial_rate_proof (v : Vault) (amount : ℚ)
    (hrate : (v.toExact.sharesTotal : ℚ) =
      v.depositNav * (10 : ℚ) ^ v.scale.toNat) :
    v.idealSharesDeposit amount = amount * (10 : ℚ) ^ v.scale.toNat := by
  unfold RawVault.idealSharesDeposit
  by_cases h : v.toExact.assetsTotal = 0
  · rw [if_pos h]
  · rw [if_neg h]
    have hpos : 0 < v.toExact.assetsTotal :=
      lt_of_le_of_ne v.exact.assetsTotal_nonneg (Ne.symm h)
    have hnav : (0 : ℚ) < v.depositNav := by
      unfold RawVault.depositNav; exact hpos
    have hne : v.depositNav ≠ 0 := hnav.ne'
    rw [hrate]; field_simp

/-- The vault `numberExponent` helper on a fractional asset returns `-100`
(zero) or a clamped IOU offset in `[-96, 80]`. -/
lemma numberExponent_fractional_offset (n : Number) (e : Int)
    (hok : numberExponent n .fractional = .ok e) :
    e = -100 ∨ ((-96 : ℤ) ≤ e ∧ e ≤ 80) := by
  unfold numberExponent at hok
  obtain ⟨a, ha, he⟩ := bind_ok_peel _ _ _ hok
  have heq : a.exponent = e :=
    Except.ok.inj (show Except.ok a.exponent = .ok e from he)
  rw [← heq]
  exact STAmount.ofNumber_fractional_offset .fractional n .to_nearest a rfl ha

/-! ## Numeric budget facts -/

/-- The deposit stage budget as a plain fraction. -/
lemma depositε_eq : depositε = 1 / 100000000000000000 := by
  unfold depositε
  rw [show ((-17) : ℤ) = -(17 : ℕ) from rfl, zpow_neg, zpow_natCast]
  norm_num

/-- The `normalize` stage error fits the deposit budget. -/
lemma εnorm_le_depositε : (5 : ℚ) / (2 ^ 63 + 7) ≤ depositε := by
  rw [depositε_eq]; norm_num

/-- Upper closure of the three-stage `mul`/`div` pipeline within `depositε`. -/
lemma deposit_pipeline_up :
    ((1 : ℚ) + 5 / (2 ^ 63 + 7)) * (1 + 6 / (2 ^ 63 - 3))
      ≤ (1 + depositε) * (1 - 6 / (2 ^ 63 - 3)) := by
  rw [depositε_eq]; norm_num

/-- Lower closure of the three-stage `mul`/`div` pipeline within `depositε`. -/
lemma deposit_pipeline_lo :
    ((1 : ℚ) - depositε) * (1 + 6 / (2 ^ 63 - 3))
      ≤ (1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3)) := by
  rw [depositε_eq]; norm_num

/-- A positive amount is stored with a clear sign bit. -/
lemma STAmount.mIsNegative_false_of_pos (a : STAmount) (h : 0 < a.toRat) :
    a.mIsNegative = false := by
  rcases hb : a.mIsNegative with _ | _
  · rfl
  · exfalso
    have := STAmount.toRat_of_neg a hb
    have hnn : (0 : ℚ) ≤ (a.mValue.toNat : ℚ) * 10 ^ a.mOffset := by positivity
    rw [this] at h
    linarith

/-- A positive-valued `Number` has a clear sign bit. -/
lemma Number.negative_false_of_pos (n : Number) (h : 0 < n.toRat) :
    n.negative_ = false := by
  rcases hb : n.negative_ with _ | _
  · rfl
  · exact absurd h (not_lt.mpr (Number.toRat_nonpos_of_negative n hb))

/-! ## Value specification of the shares side of the exchange -/

/-- **`assetsToSharesDeposit` computes `⌊q⌋` for a `q` within `depositε` of the
ideal share amount.** On a lawful vault, for a positive deposit-ready amount and
a nonzero result. The nonempty branch needs the net asset value clear of the
`Number` underflow threshold. -/
theorem assetsToSharesDeposit_spec (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (_hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hok : assetsToSharesDeposit v amount = .ok shares)
    (hnz : shares.isZero = false) :
    ∃ q : ℚ, shares.toRat = (⌊q⌋ : ℚ) ∧
      |q - v.idealSharesDeposit amount.toRat| ≤
        v.idealSharesDeposit amount.toRat * depositε ∧
      0 < v.idealSharesDeposit amount.toRat := by
  unfold assetsToSharesDeposit at hok
  have hmv : shares.mValue ≠ 0 :=
    ne_of_beq_false (show (shares.mValue == 0) = false from hnz)
  have hamv : amount.mValue ≠ 0 := by
    intro h0
    have h00 : amount.toRat = 0 := by
      rw [STAmount.toRat_signed, h0]
      simp
    exact absurd h00 (ne_of_gt hpos)
  have hnegam : amount.mIsNegative = false := STAmount.mIsNegative_false_of_pos amount hpos
  have hεd : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: shares = ⌊normalize (amount · 10^scale)⌋
    rw [if_pos hmz] at hok
    obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- the ideal
    have hA0 : v.toExact.assetsTotal = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal hmz
    have hideal : v.idealSharesDeposit amount.toRat
        = amount.toRat * (10 : ℚ) ^ (v.scale.toNat : ℕ) := by
      unfold RawVault.idealSharesDeposit
      rw [if_pos hA0]
    have hideal_pos : 0 < v.idealSharesDeposit amount.toRat := by
      rw [hideal]; positivity
    -- the normalize input denotes the ideal
    have hin : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).toRat = v.idealSharesDeposit amount.toRat := by
      rw [Number.toRat_of_nonneg _ rfl, hideal, STAmount.toRat_of_nonneg amount hnegam]
      show (amount.mValue.toNat : ℚ) * 10 ^ (amount.mOffset + (v.scale.toNat : ℤ)) = _
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
      ring
    -- the nonzero chain
    have hn2m : n2.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hmv
    have hn1m : n1.mantissa_ ≠ 0 := Number.truncate_source_ne_zero n1 n2 hn2 hn2m
    -- the normalize is `RoundsWithin` the ideal
    have hn1cast : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).normalize largeRange.min largeRange.max
          .to_nearest = .ok n1 := hn1
    have hround := normalize_rounds_to_nearest _ n1 hn1cast hn1m
    rw [hin] at hround
    have hround' : |n1.toRat - v.idealSharesDeposit amount.toRat|
        ≤ v.idealSharesDeposit amount.toRat * depositε := by
      have h1 : |n1.toRat - v.idealSharesDeposit amount.toRat|
          ≤ |v.idealSharesDeposit amount.toRat| * (5 / (2 ^ 63 + 7)) := hround
      rw [abs_of_pos hideal_pos] at h1
      refine le_trans h1 ?_
      exact mul_le_mul_of_nonneg_left εnorm_le_depositε (le_of_lt hideal_pos)
    -- n1 is positive and normalized, so truncate floors it
    have hn1pos : 0 < n1.toRat := by
      have := abs_le.mp hround'
      have hsmall : depositε < 1 := by rw [depositε_eq]; norm_num
      nlinarith [hideal_pos]
    have hn1norm : n1.isNormalized :=
      normalize_result_isNormalized _ n1 .to_nearest
        (show amount.mValue ≠ 0 from hamv) hn1cast hn1m
    obtain ⟨hn2val, hn2norm⟩ :=
      Number.truncate_floor n1 n2 hn1norm (Number.negative_false_of_pos n1 hn1pos) hn2
    -- the int64 packing is exact
    have hshval : shares.toRat = n2.toRat :=
      STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide)
        (hn2norm hn2m) (by rw [hn2val]; exact Rat.den_intCast _) hsh
    exact ⟨n1.toRat, by rw [hshval, hn2val], hround', hideal_pos⟩
  · -- nonempty vault: shares = ⌊(S·amount)/assetsTotal rounded⌋
    rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨Q, hQ, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- the divisor is `assetsTotal` exactly: there is no subtraction stage
    set navN := v.assetsTotal with hnavN_eq
    have hApos : 0 < v.toExact.assetsTotal := by
      rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
      · exact h
      · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
    have hnav_pos : 0 < v.depositNav := by
      unfold RawVault.depositNav; exact hApos
    have hS_pos : 0 < v.sharesTotal.toRat := by
      rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
      · exact h
      · exfalso
        have hz : v.toExact.sharesTotal = 0 := by
          show v.sharesTotal.toRat.num.toNat = 0
          rw [← h]
          rfl
        have := (v.exact.empty_shares hz).1
        exact absurd this.symm (ne_of_lt hApos)
    have hS_one : 1 ≤ v.sharesTotal.toRat := by
      have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hS_pos
      have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
        rw [v.wf.sharesTotal_int]
        simp
      rw [hcast]
      exact_mod_cast hnum_pos
    have hSm : v.sharesTotal.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero hS_pos.ne'
    obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
    have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
    rw [haneq] at hanval hannorm
    have hanm : amountN.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hanval]; exact hpos.ne')
    have hTm : T.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
    have hQm : Q.mantissa_ ≠ 0 := Number.truncate_source_ne_zero Q T hT hTm
    -- navN = assetsTotal exactly, so the pricing value equals depositNav with no rounding
    have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
    have hnavm : navN.mantissa_ ≠ 0 := hmz
    have hnavN_eqNav : navN.toRat = v.depositNav := by rw [hnavN_eq]; rfl
    have hnavbound : |navN.toRat - v.depositNav| ≤ v.depositNav * (6 / (2 ^ 63 - 3)) := by
      rw [hnavN_eqNav, sub_self, abs_zero]
      exact mul_nonneg (le_of_lt hnav_pos) (by norm_num)
    have hnavN_pos : 0 < navN.toRat := by rw [hnavN_eqNav]; exact hnav_pos
    -- the product stage
    have hPm : P.mantissa_ ≠ 0 := by
      intro h0
      have hsmall := operator_mul_underflow_truth_small v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSm hanm hP h0
      have hcombo : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
          = (10 : ℚ) ^ (-32750 : ℤ) := by
        rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        norm_num [minExponent]
      rw [hcombo] at hsmall
      have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ |v.sharesTotal.toRat * amountN.toRat| := by
        rw [abs_mul]
        have h1 : (1 : ℚ) ≤ |v.sharesTotal.toRat| := by
          rw [abs_of_pos hS_pos]; exact hS_one
        have h2 : (10 : ℚ) ^ (-81 : ℤ) ≤ |amountN.toRat| := by
          rw [hanval]
          exact STAmount.Canonical.abs_toRat_ge amount hc hamv
        nlinarith [abs_nonneg amountN.toRat]
      have hmono : (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-81 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      linarith
    have hPnorm : P.isNormalized :=
      operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSm hanm hP hPm
    have hPbound := operator_mul_rounds_to_nearest v.sharesTotal amountN P
      v.wf.sharesTotal_norm hannorm hP hPm
    set T0 : ℚ := v.sharesTotal.toRat * amount.toRat with hT0_def
    have hT0_pos : 0 < T0 := mul_pos hS_pos hpos
    have hPb : |P.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
      have h1 : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7)) := hPbound
      rw [hanval, ← hT0_def, abs_of_pos hT0_pos] at h1
      exact h1
    -- the division stage
    have hQbound := operator_div_rounds_to_nearest P navN Q hPnorm hnavnorm hQ hQm
    have hPpos : 0 < P.toRat := by
      have := abs_le.mp hPb
      have hε₂lt : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      nlinarith
    have hPN_pos : 0 < P.toRat / navN.toRat := div_pos hPpos hnavN_pos
    have hQpos : 0 < Q.toRat := by
      have h1 : |Q.toRat - P.toRat / navN.toRat|
          ≤ |P.toRat / navN.toRat| * (6 / (2 ^ 63 - 3)) := hQbound
      rw [abs_of_pos hPN_pos] at h1
      have := abs_le.mp h1
      nlinarith
    have h3 : |Q.toRat * navN.toRat - P.toRat| ≤ P.toRat * (6 / (2 ^ 63 - 3)) := by
      have h1 : |Q.toRat - P.toRat / navN.toRat|
          ≤ P.toRat / navN.toRat * (6 / (2 ^ 63 - 3)) := by
        have h0 := hQbound
        have h0' : |Q.toRat - P.toRat / navN.toRat|
            ≤ |P.toRat / navN.toRat| * (6 / (2 ^ 63 - 3)) := h0
        rw [abs_of_pos hPN_pos] at h0'
        exact h0'
      have h2 : |Q.toRat - P.toRat / navN.toRat| * navN.toRat
          = |Q.toRat * navN.toRat - P.toRat| := by
        have hNne : navN.toRat ≠ 0 := hnavN_pos.ne'
        rw [show Q.toRat * navN.toRat - P.toRat
          = (Q.toRat - P.toRat / navN.toRat) * navN.toRat from by field_simp]
        rw [abs_mul, abs_of_pos hnavN_pos]
      calc |Q.toRat * navN.toRat - P.toRat|
          = |Q.toRat - P.toRat / navN.toRat| * navN.toRat := h2.symm
        _ ≤ P.toRat / navN.toRat * (6 / (2 ^ 63 - 3)) * navN.toRat := by nlinarith [hnavN_pos]
        _ = P.toRat * (6 / (2 ^ 63 - 3)) := by field_simp
    -- compose the three stages
    have hcomp := div_pipeline_rel_bound v.depositNav navN.toRat T0 P.toRat Q.toRat
      (6 / (2 ^ 63 - 3)) (5 / (2 ^ 63 + 7)) (6 / (2 ^ 63 - 3)) depositε hT0_pos
      (le_of_lt hQpos) hnavbound hPb h3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) deposit_pipeline_up deposit_pipeline_lo
    -- the ideal is the exact quotient
    have hideal : v.idealSharesDeposit amount.toRat = T0 / v.depositNav := by
      unfold RawVault.idealSharesDeposit
      rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, ← hT0_def]
    have hideal_pos : 0 < v.idealSharesDeposit amount.toRat := by
      rw [hideal]; positivity
    -- floor and exact packing
    have hQnorm : Q.isNormalized :=
      operator_div_result_isNormalized P navN Q .to_nearest hPnorm hnavnorm hPm hnavm hQ hQm
    obtain ⟨hTval, hTnorm⟩ :=
      Number.truncate_floor Q T hQnorm (Number.negative_false_of_pos Q hQpos) hT
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide)
        (hTnorm hTm) (by rw [hTval]; exact Rat.den_intCast _) hsh
    refine ⟨Q.toRat, by rw [hshval, hTval], ?_, hideal_pos⟩
    rw [hideal]
    have heq1 : Q.toRat - T0 / v.depositNav
        = (Q.toRat * v.depositNav - T0) / v.depositNav := by
      field_simp
    rw [heq1, abs_div, abs_of_pos hnav_pos, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hcomp (le_of_lt hnav_pos)

/-- Proof body of `Vault.deposit_sharesIssued`: the issued shares are a
nonnegative integer within the stage budget and one truncation of the ideal. -/
theorem Vault.deposit_sharesIssued_proof (v : Vault)
    (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    (hcanon : roundedAmount.Canonical) (hpos : 0 < roundedAmount.toRat)
    (hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.sharesIssued.toRat.den = 1 ∧ 0 ≤ r.sharesIssued.toRat ∧
    v.idealSharesDeposit roundedAmount.toRat * (1 - depositε) - 1 < r.sharesIssued.toRat ∧
    r.sharesIssued.toRat ≤ v.idealSharesDeposit roundedAmount.toRat * (1 + depositε) := by
  obtain ⟨hround0, hnz0⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  obtain ⟨amount, rawAssetDeposited, c, sh, cN, sN, at', av', st', hround, _, _, _, _, hcd, _, _, _, _, _, _, _, hshr, _⟩ :=
    Vault.deposit_success_reduces v amountDeposit false r hok herr
  have hameq : amount = roundedAmount := by
    rw [hround0] at hround
    exact (Except.ok.inj hround).symm
  obtain ⟨shares, hats, hsz, _, _, hsheq⟩ :=
    computeDeposit_success_reduces v amount rawAssetDeposited sh (hcd rfl).1
  rw [hameq] at hats
  obtain ⟨q, hqval, hqbound, hqpos⟩ := assetsToSharesDeposit_spec v roundedAmount shares
    hcanon hpos hnav hats hsz
  have hshare_eq : r.sharesIssued = shares := by rw [hshr, hsheq]
  rw [hshare_eq, hqval]
  have hfl := Int.floor_le q
  have hfl2 := Int.sub_one_lt_floor q
  obtain ⟨hlo, hhi⟩ := abs_le.mp hqbound
  have hεlt : depositε < 1 := by rw [depositε_eq]; norm_num
  refine ⟨Rat.den_intCast _, ?_, ?_, ?_⟩
  · have hqpos' : 0 < q := by nlinarith
    have h0 : (0 : ℤ) ≤ ⌊q⌋ := Int.floor_nonneg.mpr (le_of_lt hqpos')
    exact_mod_cast h0
  · have h1 : v.idealSharesDeposit roundedAmount.toRat * (1 - depositε) - 1 ≤ q - 1 := by
      nlinarith
    linarith
  · have h1 : q ≤ v.idealSharesDeposit roundedAmount.toRat * (1 + depositε) := by
      nlinarith
    linarith

/-- `roundToVaultExponent` is the identity on integral amounts. -/
theorem roundToVaultExponent_integral (amountDeposit : STAmount) (assetsTotal : Number)
    (hint : amountDeposit.integral = true) :
    roundToVaultExponent amountDeposit assetsTotal = .ok amountDeposit := by
  unfold roundToVaultExponent
  rw [if_pos hint]
  rfl

/-- Proof body of `Vault.roundedDepositAmount_integral`. -/
theorem Vault.roundedDepositAmount_integral_proof (v : Vault) (amountDeposit : STAmount)
    (hint : amountDeposit.integral = true) (hnz : amountDeposit.isZero = false) :
    v.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) := by
  rw [roundedDepositAmount_ok v amountDeposit amountDeposit
      (roundToVaultExponent_integral amountDeposit v.assetsTotal hint),
    if_neg (by rw [hnz]; exact Bool.false_ne_true)]

/-- The shares side of the exchange always packs through `ofNumber .int64`, so a
successful result is a canonical `int64` record. -/
lemma assetsToSharesDeposit_int64_canonical (v : Vault) (amount shares : STAmount)
    (hok : assetsToSharesDeposit v amount = .ok shares) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 := by
  unfold assetsToSharesDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [heq] at hsh
    exact STAmount.ofNumber_integral_canonical .int64 n2 .to_nearest shares (by decide) hsh
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n4, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n5, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [heq] at hsh
    exact STAmount.ofNumber_integral_canonical .int64 n5 .to_nearest shares (by decide) hsh

/-- On an integral vault, the charge side of the exchange packs through
`checked`/`ofNumber` on the vault's type, so a successful result is a canonical
integral record of the vault's type. -/
lemma sharesToAssetsDeposit_integral_canonical (v : Vault) (shares c : STAmount)
    (hvint : v.numericType.isIntegral = true)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.IntegralCanonical ∧ c.mNumericType = v.numericType := by
  unfold sharesToAssetsDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : c' = c :=
      Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [heq] at hc
    rw [STAmount.checked] at hc
    exact STAmount.canonicalize_integral_canonical _ c .to_nearest
      (show (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hvint) hc
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n4, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : c' = c :=
      Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [heq] at hc
    exact STAmount.ofNumber_integral_canonical v.numericType n4 .upward c hvint hc

/-- The two modeled integral asset types both fit `maxRep`. -/
lemma NumericType.maxValue_le_maxRep_of_real (nt : NumericType)
    (hnt : nt = .int64 ∨ nt = .native) :
    nt.maxValue.toNat ≤ maxRep.toNat := by
  rcases hnt with h | h <;> rw [h] <;> decide

/-- Proof body of `Vault.deposit_vault_updates_integral`: in-domain integer sums
are stored exactly. -/
theorem Vault.deposit_vault_updates_integral_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hnt : v.numericType = .int64 ∨ v.numericType = .native)
    (hcanon : amountDeposit.IntegralCanonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (hdenA : v.assetsTotal.toRat.den = 1)
    (hdenAv : v.assetsAvailable.toRat.den = 1)
    (hok : v.deposit amountDeposit isDonation = .ok r) (herr : r.error = none)
    (hsz : v.toExact.assetsTotal + r.amountDeposit'.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal + r.amountDeposit'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable + r.amountDeposit'.toRat := by
  obtain ⟨amount, rawAssetDeposited, c, sh, cN, sN, at', av', st', hround, hanz, _, _, hdon, hcd,
    hcN, hsN, hat, hav, hst, hmaxg, hamt, _, hr⟩ :=
    Vault.deposit_success_reduces v amountDeposit isDonation r hok herr
  have hvint : v.numericType.isIntegral = true := by
    rcases hnt with h | h <;> rw [h] <;> decide
  -- the amount passes through `roundToVaultExponent` unchanged
  have hameq : amount = amountDeposit := by
    rw [roundToVaultExponent_integral amountDeposit v.assetsTotal hcanon.is_integral] at hround
    exact (Except.ok.inj hround).symm
  -- the taken amount is a canonical integral record of the vault's type
  have hcfacts : c.IntegralCanonical ∧ c.mNumericType = v.numericType := by
    by_cases hd : isDonation = true
    · obtain ⟨_, hceq, _⟩ := hdon hd
      rw [hceq, hameq]
      exact ⟨hcanon, hty⟩
    · have hd' : isDonation = false := by simpa using hd
      obtain ⟨hcomp, hclamp, _⟩ := hcd hd'
      obtain ⟨shares, _, _, hsta, _, _⟩ :=
        computeDeposit_success_reduces v amount rawAssetDeposited sh hcomp
      obtain ⟨hrawcanon, hrawty⟩ :=
        sharesToAssetsDeposit_integral_canonical v shares rawAssetDeposited hvint hsta
      -- For integral assets the source clamp only clears a possible sign bit.
      -- It therefore preserves representability without identifying the raw
      -- compute-stage amount with the final state-update amount.
      have hrawint : rawAssetDeposited.integral = true := hrawcanon.is_integral
      unfold clampToSumExponent at hclamp
      rw [if_pos hrawint] at hclamp
      by_cases hneg : rawAssetDeposited.negative = true
      · rw [if_pos hneg] at hclamp
        have hceq : c = rawAssetDeposited.operator_neg := (Except.ok.inj hclamp).symm
        rw [hceq]
        exact ⟨hrawcanon.operator_neg, by rw [STAmount.operator_neg_mNumericType, hrawty]⟩
      · rw [if_neg hneg] at hclamp
        have hceq : c = rawAssetDeposited := (Except.ok.inj hclamp).symm
        rw [hceq]
        exact ⟨hrawcanon, hrawty⟩
  obtain ⟨hcc, hcty⟩ := hcfacts
  have hcmax : c.mNumericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hcty]; exact NumericType.maxValue_le_maxRep_of_real v.numericType hnt
  -- `toNumber` of the taken amount is exact, normalized, integer-valued
  obtain ⟨cN', hcN', hcNval, hcNnorm, hcden⟩ :=
    STAmount.toNumber_integral_exact c .to_nearest hcc hcmax
  have hcNeq : cN' = cN := by rw [hcN'] at hcN; exact Except.ok.inj hcN
  rw [hcNeq] at hcNval hcNnorm
  -- magnitude bound on the taken amount
  have habs_c : |c.toRat| ≤ (2 : ℚ) ^ 63 - 1 := by
    refine le_trans (STAmount.IntegralCanonical.abs_toRat_le c hcc) ?_
    rw [hcty]
    rcases hnt with h | h <;> rw [h]
    · rw [show (NumericType.int64.maxValue).toNat = 9223372036854775807 from by decide]
      norm_num
    · rw [show (NumericType.native.maxValue).toNat = 100000000000000000 from by decide]
      norm_num
  have hc_r : r.amountDeposit' = c := hamt
  have hsz' : v.assetsTotal.toRat + c.toRat ≤ 2 ^ 63 - 1 := by
    rw [hc_r] at hsz; exact hsz
  have hA0 : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hAv0 : (0 : ℚ) ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAvA : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
  have hcden' : cN.toRat.den = 1 := by rw [hcNval]; exact hcden
  -- exact stored total
  have hboundA : (v.assetsTotal.toRat + cN.toRat).num.natAbs < 2 ^ 63 := by
    refine Rat.num_natAbs_lt_of_abs_le _ (Rat.den_one_add _ _ hdenA hcden') ?_
    rw [hcNval, abs_le]
    have hclo := (abs_le.mp habs_c).1
    constructor
    · linarith
    · linarith
  obtain ⟨hatval, _⟩ := operator_add_exact_int v.assetsTotal cN at'
    v.wf.assetsTotal_norm hcNnorm hdenA hcden' hboundA hat
  -- exact stored available
  have hboundAv : (v.assetsAvailable.toRat + cN.toRat).num.natAbs < 2 ^ 63 := by
    refine Rat.num_natAbs_lt_of_abs_le _ (Rat.den_one_add _ _ hdenAv hcden') ?_
    rw [hcNval, abs_le]
    have hclo := (abs_le.mp habs_c).1
    constructor
    · linarith
    · linarith
  obtain ⟨havval, _⟩ := operator_add_exact_int v.assetsAvailable cN av'
    v.wf.assetsAvailable_norm hcNnorm hdenAv hcden' hboundAv hav
  constructor
  · show r.vault'.assetsTotal.toRat = v.assetsTotal.toRat + r.amountDeposit'.toRat
    rw [hc_r, hr]
    show at'.toRat = v.assetsTotal.toRat + c.toRat
    rw [hatval, hcNval]
  · show r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.amountDeposit'.toRat
    rw [hc_r, hr]
    show av'.toRat = v.assetsAvailable.toRat + c.toRat
    rw [havval, hcNval]

/-- Proof body of `Vault.roundedDepositAmount_bounds`: the rounded amount is
`amountDeposit` floored onto a `10 ^ s` grid no coarser than the amount itself. -/
theorem Vault.roundedDepositAmount_bounds_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
      (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
    roundedAmount.isZero = false := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  refine ⟨?_, hnz⟩
  have hmv : roundedAmount.mValue ≠ 0 := by
    intro h0
    have : roundedAmount.isZero = true := by
      unfold STAmount.isZero; rw [h0]; rfl
    rw [this] at hnz; exact Bool.noConfusion hnz
  -- the self-grid witness, used by every exact-passthrough exit
  have hself : roundedAmount = amountDeposit →
      ∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
        (10 : ℚ) ^ s ≤ |roundedAmount.toRat| := by
    intro heq
    subst heq
    exact ⟨roundedAmount.exponent, STAmount.self_grid roundedAmount,
      STAmount.ulp_le_abs_toRat roundedAmount hmv⟩
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit v.assetsTotal hint] at hround
    exact hself (Except.ok.inj hround).symm
  · have hfr : amountDeposit.integral = false := by
      rcases hb : amountDeposit.integral with _ | _
      · rfl
      · exact absurd hb hint
    have hc := hcanon hfr
    unfold roundToVaultExponent at hround
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hround
    obtain ⟨_, _, hround⟩ := bind_ok_peel _ _ _ hround
    obtain ⟨postScale, hps, hround⟩ := bind_ok_peel _ _ _ hround
    have hrx := hround
    unfold postSumExponent at hps
    obtain ⟨_, _, hps⟩ := bind_ok_peel _ _ _ hps
    obtain ⟨assetsTotal', _, hps⟩ := bind_ok_peel _ _ _ hps
    -- The result is already the direct `roundToExponent` computation after
    -- the `postSumExponent` bind.
    -- the amount is nonzero (a zero amount would pass through and contradict `hnz`)
    have hz : amountDeposit.isZero = false := by
      rcases hb : amountDeposit.isZero with _ | _
      · rfl
      · exfalso
        unfold STAmount.roundToExponent at hrx
        rw [if_neg (by rw [hfr]; exact Bool.false_ne_true), if_pos hb] at hrx
        have : amountDeposit = roundedAmount := Except.ok.inj hrx
        rw [← this] at hnz
        rw [hb] at hnz
        exact Bool.noConfusion hnz
    by_cases hge : amountDeposit.exponent ≥ postScale
    · -- early exit: the amount already lives on a grid at least as fine
      apply hself
      unfold STAmount.roundToExponent at hrx
      rw [if_neg (by rw [hfr]; exact Bool.false_ne_true),
        if_neg (by rw [hz]; exact Bool.false_ne_true), if_pos hge] at hrx
      exact (Except.ok.inj hrx).symm
    · -- true truncation: the packaged grid theorem at `postScale`
      have hps_nt : numberExponent assetsTotal' .fractional = .ok postScale := by
        have hnum : amountDeposit.numericType = .fractional := hc.is_fractional
        rw [← hnum]
        exact hps
      have hps_range : (-96 : ℤ) ≤ postScale ∧ postScale ≤ 80 := by
        rcases numberExponent_fractional_offset assetsTotal' postScale hps_nt with h100 | hr
        · exfalso
          have := hc.exp_lo
          have hem : amountDeposit.exponent = amountDeposit.mOffset := rfl
          have hlt := not_le.mp hge
          omega
        · exact hr
      have hgrid := STAmount.roundToExponent_rounded amountDeposit roundedAmount postScale
        .downward hc hps_range.1 hps_range.2 hmv hrx
      refine ⟨postScale, hgrid, ?_⟩
      have hval : roundedAmount.toRat
          = (⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ) * 10 ^ postScale := hgrid
      have hne := STAmount.toRat_ne_zero roundedAmount hmv
      have hk : ⌊amountDeposit.toRat / 10 ^ postScale⌋ ≠ 0 := by
        intro h0
        rw [h0] at hval
        simp only [Int.cast_zero, zero_mul] at hval
        exact hne hval
      have hpow_pos : (0 : ℚ) < 10 ^ postScale := zpow_pos (by norm_num) _
      have habs : |roundedAmount.toRat|
          = |(⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ)| * 10 ^ postScale := by
        rw [hval, abs_mul, abs_of_pos hpow_pos]
      have hone : (1 : ℚ) ≤ |(⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (by omega)
      rw [habs]
      nlinarith

/-- A successful donation takes exactly `roundedAmount` and issues no shares. -/
theorem Vault.deposit_donation_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.amountDeposit' = roundedAmount ∧ r.sharesIssued = STAmount.zero .int64 := by
  obtain ⟨amount, rawAssetDeposited, assetDeposited, sharesCreated, cN, sN, at', av', st',
    hround, _, _, _, hdon, _, _, _, _, _, _, _, hamt, hshr, _⟩ :=
    Vault.deposit_success_reduces v amountDeposit true r hok herr
  obtain ⟨hrounded', _⟩ :=
    roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hameq : amount = roundedAmount := by
    rw [hrounded'] at hround
    exact (Except.ok.inj hround).symm
  obtain ⟨_, hasset, hshares⟩ := hdon rfl
  rw [hamt, hshr, hasset, hshares, hameq]
  exact ⟨rfl, rfl⟩

/-! ## Net-asset-value subtraction facts (shared by the shares and charge sides) -/

/-- **The deposit net asset value `navN = assetsTotal` on a nonempty lawful
vault.** It is normalized, equal to the exact positive `depositNav`, so within any
`to_nearest` budget of it (there is no subtraction stage under cash-basis). The `hnavm` witness (that the difference
did not round to zero) is available from any success that divides by it. -/
lemma Vault.depositNav_facts (v : Vault) (navN : Number)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (_hnavm : navN.mantissa_ ≠ 0)
    (hnavN : navN = v.assetsTotal) :
    navN.isNormalized ∧
      |navN.toRat - v.depositNav| ≤ v.depositNav * (6 / (2 ^ 63 - 3)) ∧
      0 < v.depositNav ∧ 0 < navN.toRat := by
  have hApos : 0 < v.toExact.assetsTotal := by
    rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
    · exact h
    · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
  have hnav_pos : 0 < v.depositNav := by unfold RawVault.depositNav; exact hApos
  have hnavN_eqNav : navN.toRat = v.depositNav := by rw [hnavN]; rfl
  refine ⟨by rw [hnavN]; exact v.wf.assetsTotal_norm, ?_, hnav_pos, ?_⟩
  · rw [hnavN_eqNav, sub_self, abs_zero]
    exact mul_nonneg (le_of_lt hnav_pos) (by norm_num)
  · rw [hnavN_eqNav]; exact hnav_pos
end XRPL.Model.SingleAssetVault
