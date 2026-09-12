import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.NumberBridge
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Sub.RoundsWithin
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg

/-! # `Vault.withdraw` accuracy proofs

Proof bodies behind the accuracy headlines in `VaultWithdraw.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `to_rep` on a non-negative `Number`: range facts

The integral `STAmount.ofNumber` path feeds `to_rep` the sign-cleared magnitude
`working`. On success the returned integer is non-negative and fits `maxRep`,
independent of normalization: the start magnitude is already clamped into
`[0, maxRep]` by `Number.mantissa`, `shift` only floor-divides, `grow` carries
its own overflow guard, the round-up bump fires only below `maxRep`, and the
cusp clamp maps down onto `maxRep`. -/

/-- `to_rep` of a sign-cleared `Number` returns an integer in `[0, maxRep]`. -/
lemma Number.to_rep_nonneg_range (n : Number) (mode : rounding_mode) (r : Int64)
    (hneg : n.negative_ = false)
    (hok : n.to_rep mode = .ok r) :
    0 ≤ r.toInt ∧ r.toInt ≤ (maxRep.toNat : ℤ) := by
  unfold Number.to_rep at hok
  simp only at hok
  by_cases hz : (n.mantissa == 0) = true
  · rw [if_pos hz] at hok
    have hr : r = 0 := by injection hok with h; exact h.symm
    rw [hr]
    refine ⟨by decide, ?_⟩
    rw [show (0 : Int64).toInt = 0 from by decide, maxRep_val]
    norm_num
  · rw [if_neg hz] at hok
    -- the start magnitude is in [0, maxRep]
    have hD0_range : 0 ≤ n.mantissa.toInt ∧ n.mantissa.toInt ≤ (maxRep.toNat : ℤ) := by
      unfold Number.mantissa
      rw [if_neg (by rw [hneg]; decide)]
      by_cases hgt : n.mantissa_ > maxRep
      · rw [if_pos hgt]
        have hlt : (n.mantissa_ / 10).toNat < 2 ^ 63 := by
          rw [UInt64.toNat_div, uint64_ten_toNat]
          have := UInt64.toNat_lt_size n.mantissa_
          rw [uint64_size_val] at this
          omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        constructor
        · exact Int.natCast_nonneg _
        · rw [UInt64.toNat_div, uint64_ten_toNat, maxRep_val]
          have := UInt64.toNat_lt_size n.mantissa_
          rw [uint64_size_val] at this
          omega
      · rw [if_neg hgt]
        have hle : n.mantissa_.toNat ≤ maxRep.toNat := by
          have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hgt)
          exact this
        have hlt : n.mantissa_.toNat < 2 ^ 63 := by rw [maxRep_val] at hle; omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        exact ⟨Int.natCast_nonneg _, by exact_mod_cast hle⟩
    rw [hneg] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    by_cases hexp : n.exponent < 0
    · have hge : ¬ n.exponent ≥ 0 := by omega
      rw [if_pos hexp, if_neg hge] at hok
      simp only at hok
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      have hDf := shift_fst_eq n.mantissa n.exponent Guard.new hD0_range.1
      rw [← hspdef] at hDf
      have hsp_nn : 0 ≤ sp.1.toInt := by
        rw [hDf]; exact Int.ediv_nonneg hD0_range.1 (by positivity)
      have hsp_le : sp.1.toInt ≤ (maxRep.toNat : ℤ) := by
        rw [hDf]
        calc n.mantissa.toInt / 10 ^ (-n.exponent).toNat ≤ n.mantissa.toInt :=
              Int.ediv_le_self _ hD0_range.1
          _ ≤ (maxRep.toNat : ℤ) := hD0_range.2
      have h_sp1_u64 : sp.1.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep sp.1 hsp_nn hsp_le
      by_cases hcusp : maxRep ≤ sp.1.toUInt64 ∧ sp.1.toUInt64 < maxRepUp
      · -- `pushOverflow` may push a digit, but the bounds argument below is uniform:
        -- the branch analysis only needs the round decision, handled per case.
        have hsp_eq : sp.1.toInt = (maxRep.toNat : ℤ) := by
          have h1 := UInt64.le_iff_toNat_le.mp hcusp.1
          have h2 : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
          omega
        rcases hb : ((sp.2.pushOverflow sp.1.toUInt64 mode).round mode == 1
            || ((sp.2.pushOverflow sp.1.toUInt64 mode).round mode == 0 && sp.1 % 2 == 1)) with _ | _
        · rw [hb] at hok
          simp only [Bool.false_eq_true, if_false] at hok
          rw [if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from by
            intro hc
            have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
            omega)] at hok
          have hr : r = sp.1 := by injection hok with h; exact h.symm
          rw [hr]; exact ⟨hsp_nn, hsp_le⟩
        · rw [hb] at hok
          simp only [if_true] at hok
          by_cases hovf : sp.1 ≥ maxRep.toInt64
          · rw [if_pos hovf] at hok; exact absurd hok (by simp)
          · exfalso
            have := (Int64.lt_iff_toInt_lt).mp (Int64.not_le.mp hovf)
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
            omega
      · have h_sp1_lt : sp.1.toUInt64.toNat < maxRep.toNat := by
          rcases lt_or_eq_of_le h_sp1_u64 with h | h
          · exact h
          · exfalso
            apply hcusp
            constructor
            · rw [UInt64.le_iff_toNat_le, h]
            · rw [UInt64.lt_iff_toNat_lt, h]
              decide
        rw [pushOverflow_noop_of_lt_maxRep h_sp1_lt sp.2 mode] at hok
        rcases hb : (sp.2.round mode == 1 || (sp.2.round mode == 0 && sp.1 % 2 == 1)) with _ | _
        · rw [hb] at hok
          simp only [Bool.false_eq_true, if_false] at hok
          rw [if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from by
            intro hc
            have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
            omega)] at hok
          have hr : r = sp.1 := by injection hok with h; exact h.symm
          rw [hr]; exact ⟨hsp_nn, hsp_le⟩
        · rw [hb] at hok
          simp only [if_true] at hok
          by_cases hovf : sp.1 ≥ maxRep.toInt64
          · rw [if_pos hovf] at hok; exact absurd hok (by simp)
          · rw [if_neg hovf] at hok
            have hovf' : sp.1.toInt < (maxRep.toNat : ℤ) := by
              have := (Int64.lt_iff_toInt_lt).mp (Int64.not_le.mp hovf)
              rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
              exact this
            have hadd : (sp.1 + 1).toInt = sp.1.toInt + 1 := by
              rw [Int64.toInt_add, int64_one_toInt, Int.bmod_eq_iff (by norm_num)]
              rw [maxRep_val] at hovf'
              refine ⟨?_, ?_⟩ <;> push_cast <;> [omega; (rw [maxRep_val] at hsp_le; omega)]
            have hr : r = sp.1 + 1 := by injection hok with h; exact h.symm
            rw [hr, hadd]
            exact ⟨by omega, by omega⟩
    · have hexp' : n.exponent ≥ 0 := not_lt.mp hexp
      rw [if_neg hexp, if_pos hexp'] at hok
      cases hgrow : Number.to_rep.grow n.mantissa n.exponent with
      | error e => rw [hgrow] at hok; exact absurd hok (by simp)
      | ok drops =>
        rw [hgrow] at hok
        simp only at hok
        have h_drops_nn : 0 ≤ drops.toInt := by
          rw [grow_ok_eq _ drops n.exponent hD0_range.1 hgrow]
          exact mul_nonneg hD0_range.1 (by positivity)
        have h_drops_le : drops.toInt ≤ (maxRep.toNat : ℤ) :=
          grow_ok_le_maxRep _ drops n.exponent hD0_range.1 hD0_range.2 hgrow
        have h_drops_u64 : drops.toUInt64.toNat ≤ maxRep.toNat :=
          toUInt64_toNat_le_maxRep drops h_drops_nn h_drops_le
        have h_g_empty : (Guard.new).empty = true := by decide
        rw [pushOverflow_noop_of_le_maxRep_of_empty h_drops_u64 Guard.new mode h_g_empty] at hok
        rw [show Guard.new.round mode = -2 from by
          have := start_guard_round mode false
          simpa using this] at hok
        rw [if_neg (show ¬ ((-2 : Int) == 1 || (-2 : Int) == 0 && drops % 2 == 1) = true from by
          simp)] at hok
        rw [if_neg (show ¬ (maxRep.toInt64 < drops ∧ drops < maxRepUp.toInt64) from by
          intro hc
          have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
          rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
          omega)] at hok
        have hr : r = drops := by injection hok with h; exact h.symm
        rw [hr]; exact ⟨h_drops_nn, h_drops_le⟩

/-! ## Integral `STAmount.ofNumber`: output shape and exact `toNumber` -/

/-- The integral `canonicalize` on an offset-`0` amount within `maxRep`
reproduces the type, keeps offset `0`, stays within `maxRep`, and preserves
the value. Structural strengthening of `canonicalize_integral_toRat`. -/
lemma STAmount.canonicalize_integral_facts (s result : STAmount) (mode : rounding_mode)
    (hint : s.integral = true) (hoff : s.mOffset = 0)
    (hval_le : s.mValue.toNat ≤ maxRep.toNat)
    (hok : s.canonicalize mode = .ok result) :
    result.mNumericType = s.mNumericType ∧ result.mOffset = 0 ∧
    result.mValue.toNat ≤ maxRep.toNat ∧ result.toRat = s.toRat := by
  have htoRat := STAmount.canonicalize_integral_toRat s result mode hint hoff hval_le hok
  rw [STAmount.canonicalize, if_pos hint] at hok
  by_cases hz : s.mValue == 0
  · rw [if_pos (by rw [hz]; rfl)] at hok
    have hres := Except.ok.inj hok
    subst hres
    exact ⟨rfl, rfl, Nat.zero_le _, htoRat⟩
  · have hz' : (s.mValue == 0) = false := by simpa using hz
    rw [if_neg (by rw [hz', hoff]; decide)] at hok
    by_cases hmoff : s.mOffset > s.mNumericType.maxOffset
    · rw [if_pos hmoff] at hok; exact absurd hok (by simp)
    rw [if_neg hmoff] at hok
    simp only [hoff, IntAmount.ofNumber] at hok
    cases hr : (Number.unchecked s.mIsNegative s.mValue 0).to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only [] at hok
      have hkey := to_rep_exact_of_exponent_zero s.mIsNegative s.mValue mode r hval_le hr
      have hnatAbs : r.toInt.natAbs = s.mValue.toNat := by
        have h1 : (r.toInt : ℚ) = (if s.mIsNegative then (-1 : ℚ) else 1) * s.mValue.toNat := hkey
        have h2 : r.toInt.natAbs = ((if s.mIsNegative then (-1 : ℤ) else 1) * s.mValue.toNat).natAbs := by
          congr 1
          exact_mod_cast (by rcases hn : s.mIsNegative <;>
            simp only [hn, Bool.false_eq_true, ↓reduceIte, Int.reduceNegSucc, neg_mul, one_mul] at h1 ⊢ <;>
            exact_mod_cast h1)
        rw [h2]
        rcases s.mIsNegative <;> simp
      by_cases hrng : r.toInt.natAbs.toUInt64 > s.mNumericType.maxValue
      · rw [if_pos hrng] at hok; exact absurd hok (by simp)
      rw [if_neg hrng] at hok
      have hres := Except.ok.inj hok
      subst hres
      refine ⟨rfl, rfl, ?_, htoRat⟩
      show (r.toInt.natAbs.toUInt64).toNat ≤ maxRep.toNat
      have hlt : r.toInt.natAbs < 2 ^ 64 := by
        rw [hnatAbs]
        have := UInt64.toNat_lt_size s.mValue
        rw [uint64_size_val] at this
        omega
      rw [UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hlt), hnatAbs]
      exact hval_le

/-- **Integral `STAmount.ofNumber` output shape.** A successful conversion into
an integral numeric type yields an offset-`0` amount of that type whose stored
magnitude fits `maxRep`. -/
lemma STAmount.ofNumber_integral_facts (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount)
    (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    result.mNumericType = nt ∧ result.mOffset = 0 ∧
    result.mValue.toNat ≤ maxRep.toNat := by
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  set neg : Bool := decide (n.signum < 0) with hneg_def
  set working : Number := if neg then n.operator_neg else n with hw_def
  have hsig : n.signum < 0 ↔ n.negative_ = true := by
    unfold Number.signum
    by_cases hnn : n.negative_ = true
    · rw [if_pos hnn]; simp [hnn]
    · rw [if_neg hnn]
      constructor
      · intro h; split at h <;> norm_num at h
      · intro h; exact absurd h hnn
  have hw_neg : working.negative_ = false := by
    rw [hw_def]
    by_cases hneg : neg = true
    · rw [if_pos hneg]
      have hnegn : n.negative_ = true :=
        hsig.mp (of_decide_eq_true (by rw [hneg_def] at hneg; exact hneg))
      unfold Number.operator_neg
      by_cases hm : (n.mantissa_ == 0) = true
      · rw [if_pos hm]; rfl
      · rw [if_neg hm]; simp [hnegn]
    · rw [if_neg hneg]
      by_cases hnegn : n.negative_ = true
      · exfalso; apply hneg; rw [hneg_def]; exact decide_eq_true (hsig.mpr hnegn)
      · simpa using hnegn
  cases hr : working.to_rep mode with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range working mode intValue hw_neg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    have hint' : (STAmount.unchecked nt intValue.toUInt64 0 neg).integral = true := hnt
    obtain ⟨h1, h2, h3, _⟩ := STAmount.canonicalize_integral_facts
      (STAmount.unchecked nt intValue.toUInt64 0 neg) result mode hint' rfl hval hok
    exact ⟨h1, h2, h3⟩

/-- **`toNumber` is value-exact, normalized, and integer-valued on an offset-`0`
integral amount within `maxRep`.** Variant of `toNumber_integral_exact` keyed on
the stored magnitude directly, so it also covers custom integral numeric types
whose carried bound exceeds `maxRep`. -/
lemma STAmount.toNumber_integral_exact' (s : STAmount) (mode : rounding_mode)
    (hint : s.mNumericType.isIntegral = true) (hoff : s.mOffset = 0)
    (hval : s.mValue.toNat ≤ maxRep.toNat) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized ∧
      s.toRat.den = 1 := by
  have hint' : s.integral = true := hint
  have hbnd : s.mValue.toNat ≤ 9223372036854775807 := by rw [maxRep_val] at hval; exact hval
  have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
  have hmax' : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
  have hsd_lo : Int64.minValue.toInt ≤ s.signedDrops := by
    unfold STAmount.signedDrops; rw [hmin]; split <;> omega
  have hsd_hi : s.signedDrops ≤ Int64.maxValue.toInt := by
    unfold STAmount.signedDrops; rw [hmax']; split <;> omega
  have hsd_toInt : s.signedDrops.toInt64.toInt = s.signedDrops :=
    XRPL.Model.Protocol.AmountArith.toInt_toInt64_self hsd_lo hsd_hi
  have h_ne_min : s.signedDrops.toInt64 ≠ Int64.minValue := by
    intro h
    have heq : s.signedDrops.toInt64.toInt = Int64.minValue.toInt := by rw [h]
    rw [hsd_toInt, hmin] at heq
    revert heq
    unfold STAmount.signedDrops
    split <;> omega
  have hroute : s.toNumber mode = IntAmount.toNumber ⟨s.signedDrops.toInt64⟩ mode := by
    unfold STAmount.toNumber STAmount.intAmount
    rw [if_pos hint', if_pos hint']
  obtain ⟨xn, hokn, hvaln, hnorm⟩ :=
    IntAmount.toNumber_exact ⟨s.signedDrops.toInt64⟩ mode h_ne_min
  have hsd_val : s.toRat = (s.signedDrops : ℚ) := by
    rw [STAmount.toRat_of_offset_zero s hoff]
  refine ⟨xn, by rw [hroute]; exact hokn, ?_, hnorm, ?_⟩
  · rw [hvaln]
    show (s.signedDrops.toInt64.toInt : ℚ) = s.toRat
    rw [hsd_toInt, hsd_val]
  · rw [hsd_val]
    exact Rat.den_intCast _

/-! ## Exact subtraction of an in-range integer from an in-range `Number` -/

/-- `J·10^ec` is a non-negative normalized `Number` for `1 ≤ J < 10^19` with the
sticky-tail condition and a small exponent window. Scaled generalization of
`Number.exists_normalized_of_pos_nat`. -/
lemma Number.exists_normalized_scaled (J : ℕ) (ec : ℤ)
    (h1 : 1 ≤ J) (h2 : J < 10 ^ 19)
    (h3 : J ≤ maxRep.toNat ∨ J % 10 = 0)
    (hlo : (-18 : ℤ) ≤ ec) (hhi : ec ≤ 0) :
    ∃ w : Number, w.isNormalized ∧ w.negative_ = false ∧
      w.toRat = (J : ℚ) * (10 : ℚ) ^ ec := by
  have hJne : J ≠ 0 := by omega
  have hlog_lo : 10 ^ Nat.log 10 J ≤ J := Nat.pow_log_le_self 10 hJne
  have hlog_hi : J < 10 ^ (Nat.log 10 J + 1) := Nat.lt_pow_succ_log_self (by norm_num) J
  set L := Nat.log 10 J with hL_def
  have hL_le : L ≤ 18 := by
    by_contra hcon
    push_neg at hcon
    have : (10 : ℕ) ^ 19 ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set k : ℕ := 18 - L with hk_def
  set M : ℕ := J * 10 ^ k with hM_def
  have hLk : L + k = 18 := by omega
  have hM_lo : 10 ^ 18 ≤ M := by
    calc (10 : ℕ) ^ 18 = 10 ^ L * 10 ^ k := by rw [← pow_add, hLk]
      _ ≤ J * 10 ^ k := mul_le_mul_of_nonneg_right hlog_lo (by positivity)
  have hM_hi : M < 10 ^ 19 := by
    calc M = J * 10 ^ k := rfl
      _ < 10 ^ (L + 1) * 10 ^ k := mul_lt_mul_of_pos_right hlog_hi (by positivity)
      _ = 10 ^ 19 := by rw [← pow_add]; congr 1; omega
  have hM_lt : M < UInt64.size := by rw [uint64_size_val]; omega
  have hM_toNat : (Nat.toUInt64 M).toNat = M :=
    UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hM_lt)
  have hsticky : Nat.toUInt64 M ≤ maxRep ∨ (Nat.toUInt64 M).toNat % 10 = 0 := by
    by_cases hk0 : k = 0
    · rcases h3 with h3 | h3
      · left
        rw [UInt64.le_iff_toNat_le, hM_toNat]
        have hMJ : M = J := by rw [hM_def, hk0, pow_zero, Nat.mul_one]
        rw [hMJ]; exact h3
      · right
        rw [hM_toNat, hM_def, hk0, pow_zero, Nat.mul_one]
        exact h3
    · right
      rw [hM_toNat]
      have hdvd : (10 : ℕ) ∣ M := by
        rw [hM_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) J
      omega
  refine ⟨⟨false, Nat.toUInt64 M, ec - (k : ℤ)⟩, ?_, rfl, ?_⟩
  · right
    refine ⟨?_, ?_, hsticky, ?_, ?_⟩
    · rw [UInt64.le_iff_toNat_le, largeRange_min_val, hM_toNat]; omega
    · rw [UInt64.le_iff_toNat_le, largeRange_max_val, hM_toNat]; omega
    · show minExponent ≤ ec - (k : ℤ); unfold minExponent; omega
    · show ec - (k : ℤ) ≤ maxExponent; unfold maxExponent; omega
  · rw [Number.toRat_of_nonneg _ rfl]
    show ((Nat.toUInt64 M).toNat : ℚ) * (10 : ℚ) ^ (ec - (k : ℤ)) = (J : ℚ) * (10 : ℚ) ^ ec
    rw [hM_toNat, hM_def, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    push_cast
    have h10k : (0 : ℚ) < (10 : ℚ) ^ k := by positivity
    field_simp

/-- **Exact subtraction of an integer within the int64 window.** For a normalized
`x` with `0 ≤ x ≤ 2^63 - 1` and an integer value `0 ≤ k ≤ x` held in a
normalized `aN`, the `to_nearest` subtraction returns exactly `x - k`: the
difference is representable, so the correctly-rounded result equals it.
(`0 ≤ x` is implied by `0 ≤ k ≤ x`.) -/
lemma operator_sub_exact_int_le (x aN result : Number) (k : ℚ)
    (hx : x.isNormalized) (hxle : x.toRat ≤ 2 ^ 63 - 1)
    (haN : aN.isNormalized) (haN_val : aN.toRat = k)
    (hk_int : k.den = 1) (hknn : 0 ≤ k) (hkle : k ≤ x.toRat)
    (hok : x.operator_sub aN .to_nearest = .ok result) :
    result.toRat = x.toRat - k := by
  have hrtr := operator_sub_rounded_to_nearest x aN result hx haN hok
  rw [haN_val] at hrtr
  -- a representable witness for x - k closes the goal
  suffices hwit : ∃ w : Number, w.isNormalized ∧ w.toRat = x.toRat - k by
    obtain ⟨w, hw_norm, hw_val⟩ := hwit
    exact Number.RoundsToRepresentable.eq_of_representable result _ hrtr w hw_norm hw_val
  by_cases hk0 : k = 0
  · exact ⟨x, hx, by rw [hk0, sub_zero]⟩
  have hk1 : 1 ≤ k := by
    have hnum_pos : 0 < k.num := by
      rcases lt_trichotomy k.num 0 with h | h | h
      · exact absurd (Rat.num_nonneg.mpr hknn) (by omega)
      · exact absurd (Rat.zero_iff_num_zero.mpr h) hk0
      · exact h
    have : (1 : ℚ) ≤ (k.num : ℚ) := by exact_mod_cast hnum_pos
    calc (1 : ℚ) ≤ (k.num : ℚ) := this
      _ = k := by
        conv_rhs => rw [← Rat.num_div_den k]
        rw [hk_int]; push_cast; ring
  have hx_mne : x.mantissa_ ≠ 0 := by
    intro h0
    have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx h0
    rw [hx0, Number.toRat_zero] at hkle
    linarith
  have hx_neg : x.negative_ = false := by
    by_contra hc
    have hc' : x.negative_ = true := by simpa using hc
    have := Number.toRat_of_neg x hc'
    have hmpos : 0 < (x.mantissa_.toNat : ℚ) := by
      have : 0 < x.mantissa_.toNat := by
        have := (hx.mantissaBounds_nat hx_mne).1; omega
      exact_mod_cast this
    nlinarith [zpow_pos (show (0:ℚ) < 10 from by norm_num) x.exponent_,
      le_trans hknn hkle]
  have hx_val : x.toRat = (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ x.exponent_ :=
    Number.toRat_of_nonneg x hx_neg
  obtain ⟨hmA_lo, hmA_hi⟩ := hx.mantissaBounds_nat hx_mne
  have hexp_range : minExponent ≤ x.exponent_ ∧ x.exponent_ ≤ maxExponent := by
    rcases hx with h_zero | ⟨_, _, _, hlo, hhi⟩
    · exact absurd (show x.mantissa_ = 0 by rw [h_zero]; rfl) hx_mne
    · exact ⟨hlo, hhi⟩
  set eA := x.exponent_ with heA_def
  have heA_le : eA ≤ 0 := by
    by_contra hc
    push_neg at hc
    have h10 : (10 : ℚ) ^ (1 : ℤ) ≤ (10 : ℚ) ^ eA := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hm18 : ((10 : ℕ) ^ 18 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by exact_mod_cast hmA_lo
    rw [hx_val] at hxle
    push_cast at hm18
    nlinarith [hxle, h10, hm18]
  have heA_ge : (-18 : ℤ) ≤ eA := by
    by_contra hc
    push_neg at hc
    have h10 : (10 : ℚ) ^ eA ≤ (10 : ℚ) ^ (-19 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hm19 : (x.mantissa_.toNat : ℚ) < ((10 : ℕ) ^ 19 : ℚ) := by exact_mod_cast hmA_hi
    have hxlt : x.toRat < 1 := by
      rw [hx_val]
      push_cast at hm19
      calc (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ eA
          < 10 ^ 19 * (10 : ℚ) ^ (-19 : ℤ) := by
            have hmnn : (0 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by positivity
            have hppos : (0 : ℚ) < (10 : ℚ) ^ eA := zpow_pos (by norm_num) _
            nlinarith [h10, hm19, hppos]
        _ = 1 := by
            rw [show ((10 : ℚ) ^ 19 : ℚ) = (10 : ℚ) ^ (19 : ℤ) from by norm_num,
              ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
            norm_num
    linarith
  -- the integer k scaled onto x's grid
  set K : ℕ := k.num.toNat with hK_def
  have hK_val : (K : ℚ) = k := by
    rw [hK_def]
    have : (k.num.toNat : ℤ) = k.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hknn)
    have hq : ((k.num.toNat : ℤ) : ℚ) = (k.num : ℚ) := by exact_mod_cast this
    push_cast at hq ⊢
    rw [hq]
    conv_rhs => rw [← Rat.num_div_den k]
    rw [hk_int]; push_cast; ring
  set KK : ℕ := K * 10 ^ (-eA).toNat with hKK_def
  have hpow_eq : ((10 : ℚ) ^ (-eA).toNat) * (10 : ℚ) ^ eA = 1 := by
    rw [← zpow_natCast (10 : ℚ) (-eA).toNat, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    rw [show ((-eA).toNat : ℤ) + eA = 0 from by omega]
    norm_num
  have hKK_le : KK ≤ x.mantissa_.toNat := by
    have hcross : (KK : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by
      rw [hKK_def]
      push_cast
      have h1 : (K : ℚ) * ((10 : ℚ) ^ (-eA).toNat) * (10 : ℚ) ^ eA ≤
          (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ eA := by
        rw [mul_assoc, hpow_eq, mul_one, hK_val, ← hx_val]
        exact hkle
      have hppos : (0 : ℚ) < (10 : ℚ) ^ eA := zpow_pos (by norm_num) _
      exact le_of_mul_le_mul_right (by rw [mul_assoc] at h1 ⊢; exact h1) hppos
    exact_mod_cast hcross
  set J : ℕ := x.mantissa_.toNat - KK with hJ_def
  have hJ_val : (J : ℚ) * (10 : ℚ) ^ eA = x.toRat - k := by
    rw [hJ_def, hx_val]
    push_cast [Nat.cast_sub hKK_le]
    rw [hKK_def]
    push_cast
    rw [sub_mul, mul_assoc, hpow_eq, mul_one, hK_val]
  by_cases hJ0 : J = 0
  · refine ⟨Number.zero, Or.inl rfl, ?_⟩
    rw [Number.toRat_zero, ← hJ_val, hJ0]
    norm_num
  have hsticky : J ≤ maxRep.toNat ∨ J % 10 = 0 := by
    by_cases hJle : J ≤ maxRep.toNat
    · exact Or.inl hJle
    · right
      push_neg at hJle
      have hmA_gt : maxRep.toNat < x.mantissa_.toNat := by
        have : J ≤ x.mantissa_.toNat := by rw [hJ_def]; omega
        omega
      have heA_neg : eA ≤ -1 := by
        by_contra hc
        push_neg at hc
        have heA0 : eA = 0 := by omega
        have hxq : x.toRat = (x.mantissa_.toNat : ℚ) := by
          rw [hx_val, heA0]; norm_num
        rw [hxq] at hxle
        have hlt : (x.mantissa_.toNat : ℚ) < 2 ^ 63 := by linarith
        have : x.mantissa_.toNat < 2 ^ 63 := by exact_mod_cast hlt
        rw [maxRep_val] at hmA_gt
        omega
      have hmA_mod : x.mantissa_.toNat % 10 = 0 := by
        rcases hx with h_zero | ⟨_, _, hst, _, _⟩
        · exact absurd (show x.mantissa_ = 0 by rw [h_zero]; rfl) hx_mne
        · rcases hst with hst | hst
          · exact absurd (UInt64.le_iff_toNat_le.mp hst) (by omega)
          · exact hst
      have hKK_dvd : (10 : ℕ) ∣ KK := by
        rw [hKK_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) K
      have hmA_dvd : (10 : ℕ) ∣ x.mantissa_.toNat := Nat.dvd_of_mod_eq_zero hmA_mod
      rw [hJ_def]
      obtain ⟨a, ha⟩ := hmA_dvd
      obtain ⟨b, hb⟩ := hKK_dvd
      rw [ha, hb]
      omega
  obtain ⟨w, hw_norm, _, hw_val⟩ := Number.exists_normalized_scaled J eA
    (by omega) (by rw [hJ_def]; omega) hsticky heA_ge heA_le
  exact ⟨w, hw_norm, by rw [hw_val, hJ_val]⟩

/-! ## `withdraw_sharesBurned_exact` proof body -/

/-- **Proof body of `withdraw_sharesBurned_exact`.** A successful share-denominated
withdrawal burns exactly the named shares: the reduction echoes the named amount
through `computeWithdrawByShares`. -/
theorem Vault.withdraw_sharesBurned_exact_proof (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned = shares := by
  obtain ⟨cw, an, sta, hcomp, herr2, -, -, -, hsb, -⟩ :=
    Vault.withdraw_success_reduces v (.vaultShares shares) waiveUnrealizedLoss r hok herr
  obtain ⟨-, hshares⟩ :=
    computeWithdrawByShares_none_reduces v shares waiveUnrealizedLoss cw hcomp herr2
  rw [hsb, hshares]

/-! ## `withdraw_vault_updates_integral` proof body -/

/-- The `sharesToAssetsWithdraw` output for an integral vault is an offset-`0`
amount of the vault's numeric type within `maxRep`: the zero-NAV exit returns
the canonical zero, the regular exit an integral `ofNumber` result. -/
lemma Vault.sharesToAssetsWithdraw_integral_shape (v : Vault) (sh assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hint : v.numericType.isIntegral = true)
    (hok : v.sharesToAssetsWithdraw sh waiveUnrealizedLoss = .ok assets) :
    assets.mNumericType = v.numericType ∧ assets.mOffset = 0 ∧
    assets.mValue.toNat ≤ maxRep.toNat := by
  obtain ⟨nav, -, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v sh assets waiveUnrealizedLoss hok
  rcases hcase with ⟨-, hzero⟩ | ⟨-, sn, nv, an, -, -, -, hof⟩
  · subst hzero
    refine ⟨?_, ?_, ?_⟩
    · cases v.numericType with
      | fractional => rfl
      | integral mv mo ms msh => rfl
    · cases hnt : v.numericType with
      | fractional => rw [hnt] at hint; exact absurd hint (by decide)
      | integral mv mo ms msh => rfl
    · rw [STAmount.zero_mValue]
      exact Nat.zero_le _
  · exact STAmount.ofNumber_integral_facts v.numericType an .downward assets hint hof

/-- **Proof body of `withdraw_vault_updates_integral`.** The withdraw model
first checks availability against the raw payout, then clamps the negated payout
and subtracts the resulting final debit.  The raw and final amounts are not
identical in general, so this theorem records the final-debit provenance and the
correct-to-nearest state-update relation rather than asserting a false clamp
identity. -/
theorem Vault.withdraw_vault_updates_integral_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assets'.toRat)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    ∃ (cw : ComputeWithdrawResult) (assetDebited : STAmount) (assetDebitedNumber : Number),
      (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss) = .ok cw ∧
      cw.error = none ∧
      clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok assetDebited ∧
      assetDebited.isFractionalNonPositive = .ok false ∧
      assetDebited.toNumber .to_nearest = .ok assetDebitedNumber ∧
      r.assets' = assetDebited ∧
      Number.RoundsToRepresentable r.vault'.assetsTotal
        (v.assetsTotal.toRat - r.assets'.toRat) .to_nearest ∧
      Number.RoundsToRepresentable r.vault'.assetsAvailable
        (v.assetsAvailable.toRat - r.assets'.toRat) .to_nearest := by
  obtain ⟨cw, rawAssetsNumber, sta, hcomp, herr2, hraw, hlt, hsta, hsb, hdisj⟩ :=
    Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr
  -- The share-total conversion is deterministic, so the success branch is non-final.
  have hsta_eq : sta = sharesTotalAmount := by
    rw [hst] at hsta
    exact (Except.ok.inj hsta).symm
  subst hsta_eq
  rcases hdisj with ⟨hfin', -⟩ |
      ⟨-, sharesBurnedNumber, assetDebitedNumber, assetsTotal', assetsAvailable', sharesTotal',
        assetDebited, assetsTotalRounded, assetsTotalRounded', hsbn, hclamp, hprecision,
        hdebitNumber, hat, hatr, hatr', hguard, hav, hshares, hr_assets, hr⟩
  · rw [← hsb] at hfin'
    rw [hfin'] at hfin
    exact absurd hfin (by simp)
  · have hassets : ∃ sh : STAmount,
      v.sharesToAssetsWithdraw sh waiveUnrealizedLoss = .ok cw.assets' := by
      cases amount with
      | vaultAssets a =>
        obtain ⟨shares, -, -, hs, -⟩ :=
          computeWithdrawByAssets_none_reduces v a waiveUnrealizedLoss cw hcomp herr2
        exact ⟨shares, hs⟩
      | vaultShares s =>
        obtain ⟨hs, -⟩ :=
          computeWithdrawByShares_none_reduces v s waiveUnrealizedLoss cw hcomp herr2
        exact ⟨s, hs⟩
    obtain ⟨sh, hsh⟩ := hassets
    obtain ⟨hshape_nt, hshape_off, hshape_val⟩ :=
      Vault.sharesToAssetsWithdraw_integral_shape v sh cw.assets' waiveUnrealizedLoss hint hsh
    -- The clamp sees an integral input and therefore returns its absolute form;
    -- this supplies final-debit representation facts, not raw-payout identity.
    have hneg_integral : cw.assets'.operator_neg.integral = true := by
      change cw.assets'.operator_neg.mNumericType.isIntegral = true
      rw [STAmount.operator_neg_mNumericType, hshape_nt]
      exact hint
    have hdebit_eq : assetDebited =
        if cw.assets'.operator_neg.negative then cw.assets'.operator_neg.operator_neg
        else cw.assets'.operator_neg := by
      unfold clampToSumExponent at hclamp
      simp only [hneg_integral, ↓reduceIte] at hclamp
      exact (Except.ok.inj hclamp).symm
    have hdebit_nt : assetDebited.mNumericType = v.numericType := by
      rw [hdebit_eq]
      split <;> simp [STAmount.operator_neg_mNumericType, hshape_nt]
    have hdebit_off : assetDebited.mOffset = 0 := by
      rw [hdebit_eq]
      split <;> simp [STAmount.operator_neg_mOffset, hshape_off]
    have hdebit_val : assetDebited.mValue.toNat ≤ maxRep.toNat := by
      rw [hdebit_eq]
      split <;> simp [STAmount.operator_neg_mValue, hshape_val]
    obtain ⟨debitNumber, hdebit_ok, hdebit_val, hdebit_norm, hdebit_den⟩ :=
      STAmount.toNumber_integral_exact' assetDebited .to_nearest
        (by rw [hdebit_nt]; exact hint) hdebit_off hdebit_val
    have hdebit_eq_number : assetDebitedNumber = debitNumber := by
      rw [hdebit_ok] at hdebitNumber
      exact (Except.ok.inj hdebitNumber).symm
    subst assetDebitedNumber
    refine ⟨cw, assetDebited, debitNumber, hcomp, herr2, hclamp, hprecision,
      hdebit_ok, hr_assets, ?_, ?_⟩
    · simpa [hr, hr_assets, hdebit_val] using
        (operator_sub_rounded_to_nearest v.assetsTotal debitNumber assetsTotal'
          v.wf.assetsTotal_norm hdebit_norm hat)
    · simpa [hr, hr_assets, hdebit_val] using
        (operator_sub_rounded_to_nearest v.assetsAvailable debitNumber assetsAvailable'
          v.wf.assetsAvailable_norm hdebit_norm hav)

end XRPL.Model.SingleAssetVault
