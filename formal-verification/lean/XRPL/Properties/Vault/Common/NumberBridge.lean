import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.Bounds
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Add.Common.Rounded
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.SameSign
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable

/-! # Number rounding bridge for the vault proofs

Reusable `to_nearest` facts about `Number.operator_add` / `operator_sub`, phrased
against the grid characterization (`Number.lower` / `Number.upper` tightness). The
vault reductions need three things the `Number` tree only proves inline inside
`Add/Common/DirectedTight.lean`:

* **grid minimality** — a `to_nearest` rounding never crosses a normalized point the
  exact value was already on the far side of;
* **sign preservation** — a `to_nearest` rounding of a non-negative value is
  non-negative;
* **exact integer arithmetic** — sums / differences of small integers are stored
  with no rounding error.

Monotonicity of `to_nearest` is deliberately absent: the `RoundsToRepresentable`
predicate is a disjunction (`result` is *either* neighbor), so at a tie the two
operands could round to opposite neighbors, and the predicate does not pin the
"nearest" choice needed for monotonicity. -/

namespace XRPL.Model.Protocol

/-! ## Grid minimality on `RoundsToRepresentable … to_nearest` -/

/-- **Grid upper minimality.** A `to_nearest` rounding of `z` never lands above a
normalized point `m` that already dominates `z`. -/
lemma Number.RoundsToRepresentable.le_of_le_normalized (result : Number) (z : ℚ)
    (hr : Number.RoundsToRepresentable result z .to_nearest)
    (m : Number) (hm : m.isNormalized) (hle : z ≤ m.toRat) :
    result.toRat ≤ m.toRat := by
  rcases hr with ⟨n, hlo, hval⟩ | ⟨n, hup, hval⟩
  · rw [hval]; exact le_trans (Number.lower_le z n hlo) hle
  · rw [hval]; exact Number.upper_tight z n hup m hm hle

/-- **Grid lower maximality.** A `to_nearest` rounding of `z` never lands below a
normalized point `m` already dominated by `z`. -/
lemma Number.RoundsToRepresentable.ge_of_ge_normalized (result : Number) (z : ℚ)
    (hr : Number.RoundsToRepresentable result z .to_nearest)
    (m : Number) (hm : m.isNormalized) (hge : m.toRat ≤ z) :
    m.toRat ≤ result.toRat := by
  rcases hr with ⟨n, hlo, hval⟩ | ⟨n, hup, hval⟩
  · rw [hval]; exact Number.lower_tight z n hlo m hm hge
  · rw [hval]; exact le_trans hge (Number.le_upper z n hup)

/-- **Sign preservation.** A `to_nearest` rounding of a non-negative value is
non-negative. -/
lemma Number.RoundsToRepresentable.nonneg_of_nonneg (result : Number) (z : ℚ)
    (hr : Number.RoundsToRepresentable result z .to_nearest) (hz : 0 ≤ z) :
    0 ≤ result.toRat := by
  have h := Number.RoundsToRepresentable.ge_of_ge_normalized result z hr Number.zero
    (Or.inl rfl) (by rw [Number.toRat_zero]; exact hz)
  rwa [Number.toRat_zero] at h

/-- **Sign preservation, non-positive side.** -/
lemma Number.RoundsToRepresentable.nonpos_of_nonpos (result : Number) (z : ℚ)
    (hr : Number.RoundsToRepresentable result z .to_nearest) (hz : z ≤ 0) :
    result.toRat ≤ 0 := by
  have h := Number.RoundsToRepresentable.le_of_le_normalized result z hr Number.zero
    (Or.inl rfl) (by rw [Number.toRat_zero]; exact hz)
  rwa [Number.toRat_zero] at h

/-! ## Integer representability -/

/-- Any positive integer below `2^63` is the value of a non-negative normalized
`Number`. The mantissa `V·10^k` with `k = 18 - ⌊log₁₀ V⌋` lands in
`[10^18, 10^19)`; when `k ≥ 1` it is divisible by 10 and when `k = 0` we have
`V ≤ maxRep`, so the sticky-tail normalization condition holds either way. -/
lemma Number.exists_normalized_of_pos_nat (V : ℕ) (h1 : 1 ≤ V) (h2 : V < 2 ^ 63) :
    ∃ w : Number, w.isNormalized ∧ w.negative_ = false ∧ w.toRat = (V : ℚ) := by
  have hVne : V ≠ 0 := by omega
  have hlog_lo : 10 ^ Nat.log 10 V ≤ V := Nat.pow_log_le_self 10 hVne
  have hlog_hi : V < 10 ^ (Nat.log 10 V + 1) := Nat.lt_pow_succ_log_self (by norm_num) V
  set L := Nat.log 10 V with hL_def
  have hL_le : L ≤ 18 := by
    by_contra hcon
    push_neg at hcon
    have : (10 : ℕ) ^ 19 ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h63 : (2 : ℕ) ^ 63 < 10 ^ 19 := by norm_num
    omega
  set k : ℕ := 18 - L with hk_def
  set M : ℕ := V * 10 ^ k with hM_def
  have hLk : L + k = 18 := by omega
  have hM_lo : 10 ^ 18 ≤ M := by
    calc (10 : ℕ) ^ 18 = 10 ^ L * 10 ^ k := by rw [← pow_add, hLk]
      _ ≤ V * 10 ^ k := mul_le_mul_of_nonneg_right hlog_lo (by positivity)
  have hM_hi : M < 10 ^ 19 := by
    calc M = V * 10 ^ k := rfl
      _ < 10 ^ (L + 1) * 10 ^ k := mul_lt_mul_of_pos_right hlog_hi (by positivity)
      _ = 10 ^ 19 := by rw [← pow_add]; congr 1; omega
  have hM_lt : M < UInt64.size := by rw [uint64_size_val]; omega
  have hM_toNat : (Nat.toUInt64 M).toNat = M :=
    UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hM_lt)
  have hsticky : (Nat.toUInt64 M).toNat ≤ maxRep.toNat ∨ (Nat.toUInt64 M).toNat % 10 = 0 := by
    rw [hM_toNat]
    by_cases hk0 : k = 0
    · left
      rw [maxRep_val]
      have hMV : M = V := by rw [hM_def, hk0, pow_zero, Nat.mul_one]
      rw [hMV]; omega
    · right
      have hdvd : (10 : ℕ) ∣ M := by
        rw [hM_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) V
      omega
  refine ⟨⟨false, Nat.toUInt64 M, -(k : ℤ)⟩, ?_, rfl, ?_⟩
  · right
    refine ⟨?_, ?_, hsticky, ?_, ?_⟩
    · rw [UInt64.le_iff_toNat_le, largeRange_min_val, hM_toNat]; omega
    · rw [UInt64.le_iff_toNat_le, largeRange_max_val, hM_toNat]; omega
    · show minExponent ≤ -(k : ℤ); unfold minExponent; omega
    · show -(k : ℤ) ≤ maxExponent; unfold maxExponent; omega
  · rw [Number.toRat_of_nonneg _ rfl]
    show ((Nat.toUInt64 M).toNat : ℚ) * (10 : ℚ) ^ (-(k : ℤ)) = (V : ℚ)
    rw [hM_toNat, hM_def, zpow_neg, zpow_natCast]
    push_cast
    field_simp

/-- Any integer of magnitude below `2^63` is the value of a normalized `Number`. -/
lemma Number.exists_normalized_of_int (V : ℤ) (h : V.natAbs < 2 ^ 63) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (V : ℚ) := by
  rcases lt_trichotomy V 0 with hneg | hzero | hpos
  · obtain ⟨w0, hw0_norm, hw0_neg, hw0_val⟩ :=
      Number.exists_normalized_of_pos_nat (-V).toNat (by omega) (by omega)
    have hcast : (((-V).toNat : ℤ) : ℚ) = -(V : ℚ) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    refine ⟨⟨true, w0.mantissa_, w0.exponent_⟩, ?_, ?_⟩
    · rcases hw0_norm with hz | hfields
      · exfalso
        rw [hz, Number.toRat_zero] at hw0_val
        have hnz : ((-V).toNat : ℚ) = 0 := hw0_val.symm
        have : (-V).toNat = 0 := by exact_mod_cast hnz
        omega
      · exact Or.inr hfields
    · rw [Number.toRat_of_neg _ rfl,
        ← Number.toRat_of_nonneg w0 hw0_neg, hw0_val]
      rw [show (((-V).toNat : ℕ) : ℚ) = (((-V).toNat : ℤ) : ℚ) by push_cast; ring, hcast]
      ring
  · exact ⟨Number.zero, Or.inl rfl, by rw [Number.toRat_zero, hzero]; norm_num⟩
  · obtain ⟨w, hw_norm, _, hw_val⟩ :=
      Number.exists_normalized_of_pos_nat V.toNat (by omega) (by omega)
    refine ⟨w, hw_norm, ?_⟩
    rw [hw_val, show ((V.toNat : ℕ) : ℚ) = ((V.toNat : ℤ) : ℚ) by push_cast; ring,
      Int.toNat_of_nonneg (le_of_lt hpos)]

/-- **Exact on representable targets.** If the exact value `z` equals the value of
some normalized `Number`, then any `to_nearest` rounding of `z` is exactly `z`. -/
lemma Number.RoundsToRepresentable.eq_of_representable (result : Number) (z : ℚ)
    (hr : Number.RoundsToRepresentable result z .to_nearest)
    (w : Number) (hw : w.isNormalized) (hwz : w.toRat = z) :
    result.toRat = z := by
  have h1 : result.toRat ≤ z :=
    hwz ▸ Number.RoundsToRepresentable.le_of_le_normalized result z hr w hw (le_of_eq hwz.symm)
  have h2 : z ≤ result.toRat :=
    hwz ▸ Number.RoundsToRepresentable.ge_of_ge_normalized result z hr w hw (le_of_eq hwz)
  exact le_antisymm h1 h2

/-! ## `operator_add` / `operator_sub` connectors (`to_nearest`) -/

/-- Grid minimality for a `to_nearest` addition: the rounded sum stays under a
normalized ceiling the exact sum was under. -/
lemma operator_add_le_of_le_normalized (x y result m : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (hm : m.isNormalized) (hle : x.toRat + y.toRat ≤ m.toRat) :
    result.toRat ≤ m.toRat :=
  Number.RoundsToRepresentable.le_of_le_normalized result (x.toRat + y.toRat)
    (operator_add_rounded_to_nearest x y result hx hy hok) m hm hle

/-- Grid maximality for a `to_nearest` addition. -/
lemma operator_add_ge_of_ge_normalized (x y result m : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (hm : m.isNormalized) (hge : m.toRat ≤ x.toRat + y.toRat) :
    m.toRat ≤ result.toRat :=
  Number.RoundsToRepresentable.ge_of_ge_normalized result (x.toRat + y.toRat)
    (operator_add_rounded_to_nearest x y result hx hy hok) m hm hge

/-- A `to_nearest` addition of a non-negative exact sum is non-negative. -/
lemma operator_add_nonneg (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (hnn : 0 ≤ x.toRat + y.toRat) :
    0 ≤ result.toRat :=
  Number.RoundsToRepresentable.nonneg_of_nonneg result (x.toRat + y.toRat)
    (operator_add_rounded_to_nearest x y result hx hy hok) hnn

/-- A `to_nearest` subtraction that stays under a normalized ceiling. -/
lemma operator_sub_le_of_le_normalized (x y result m : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hm : m.isNormalized) (hle : x.toRat - y.toRat ≤ m.toRat) :
    result.toRat ≤ m.toRat :=
  Number.RoundsToRepresentable.le_of_le_normalized result (x.toRat - y.toRat)
    (operator_sub_rounded_to_nearest x y result hx hy hok) m hm hle

/-- A `to_nearest` subtraction that stays above a normalized floor. -/
lemma operator_sub_ge_of_ge_normalized (x y result m : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hm : m.isNormalized) (hge : m.toRat ≤ x.toRat - y.toRat) :
    m.toRat ≤ result.toRat :=
  Number.RoundsToRepresentable.ge_of_ge_normalized result (x.toRat - y.toRat)
    (operator_sub_rounded_to_nearest x y result hx hy hok) m hm hge

/-- A `to_nearest` subtraction of a non-negative exact difference is
non-negative. -/
lemma operator_sub_nonneg (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hnn : 0 ≤ x.toRat - y.toRat) :
    0 ≤ result.toRat :=
  Number.RoundsToRepresentable.nonneg_of_nonneg result (x.toRat - y.toRat)
    (operator_sub_rounded_to_nearest x y result hx hy hok) hnn

/-! ## Result normalization (both signs)

`operator_add_result_isNormalized` in the `Number` tree only covers the
diff-sign branch. The vault lawfulness clauses need the general fact: any
nonzero `to_nearest` add/sub of normalized operands is normalized. The same-sign
branch is picked up from the algorithmic facts (which carry `result.isNormalized`
directly), the diff-sign branch from the existing lemma, and the zero/cancellation
guards return an operand or the canonical zero. -/

/-- **General-sign add normalization (`to_nearest`).** A nonzero-mantissa
`to_nearest` sum of two normalized operands is normalized, regardless of the
operands' relative sign. -/
lemma operator_add_isNormalized_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    result.isNormalized := by
  -- Zero-`y` guard: result = x.
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hx
  -- Zero-`x` guard: result = y.
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hy
  -- Exact cancellation: result = Number.zero, excluded by `hresult`.
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · have h_result : result = Number.zero := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
      exact (Except.ok.inj
        (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
    exact absurd (show result.mantissa_ = 0 by rw [h_result]; rfl) hresult
  -- Generic path.
  have hx_mant_ne : x.mantissa_ ≠ 0 := by
    intro h
    apply hx_guard
    have hx_zero : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx h
    rw [hx_zero]; decide
  have hy_mant_ne : y.mantissa_ ≠ 0 := by
    intro h
    apply hy_guard
    have hy_zero : y = Number.zero := Number.eq_zero_of_mantissa_zero y hy h
    rw [hy_zero]; decide
  by_cases h_sign_eq : x.negative_ = y.negative_
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_norm, _⟩ :=
      operator_add_algorithmic_facts_same_sign_to_nearest x y result hx hy hx_mant_ne hy_mant_ne
        h_sign_eq heq_guard hok
    exact h_norm
  · exact operator_add_result_isNormalized x y result .to_nearest hx hy hx_mant_ne hy_mant_ne
      h_sign_eq heq_guard hok hresult

/-- **General-sign sub normalization (`to_nearest`).** A nonzero-mantissa
`to_nearest` difference of two normalized operands is normalized. Reduces to the
add case via `operator_sub x y = operator_add x (-y)`. -/
lemma operator_sub_isNormalized_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    result.isNormalized := by
  unfold Number.operator_sub at hok
  exact operator_add_isNormalized_to_nearest x y.operator_neg result hx
    (Number.operator_neg_isNormalized y hy) hok hresult

/-! ## Exact integer arithmetic -/

/-- An integer-valued normalized `Number` equals the cast of its numerator. -/
private lemma toRat_eq_num_cast (x : Number) (hxd : x.toRat.den = 1) :
    x.toRat = (x.toRat.num : ℚ) := by
  conv_lhs => rw [← Rat.num_div_den x.toRat]
  rw [hxd, Nat.cast_one, div_one]

/-- **Exact integer addition.** When both operands are integer-valued and the
integer sum fits `19` digits (below `2^63`), the `to_nearest` sum is stored with
no rounding error and stays integer-valued. -/
lemma operator_add_exact_int (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxd : x.toRat.den = 1) (hyd : y.toRat.den = 1)
    (hbound : (x.toRat + y.toRat).num.natAbs < 2 ^ 63)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    result.toRat = x.toRat + y.toRat ∧ result.toRat.den = 1 := by
  have hxq := toRat_eq_num_cast x hxd
  have hyq := toRat_eq_num_cast y hyd
  have hsum_eq : x.toRat + y.toRat = ((x.toRat.num + y.toRat.num : ℤ) : ℚ) := by
    conv_lhs => rw [hxq, hyq]
    push_cast; ring
  have hnum : (x.toRat + y.toRat).num = x.toRat.num + y.toRat.num := by
    rw [hsum_eq]; exact Rat.num_intCast _
  have hbound' : (x.toRat.num + y.toRat.num).natAbs < 2 ^ 63 := by rw [← hnum]; exact hbound
  obtain ⟨w, hw_norm, hw_val⟩ := Number.exists_normalized_of_int _ hbound'
  have hw_val' : w.toRat = x.toRat + y.toRat := by rw [hw_val, ← hsum_eq]
  have hres : result.toRat = x.toRat + y.toRat :=
    Number.RoundsToRepresentable.eq_of_representable result _
      (operator_add_rounded_to_nearest x y result hx hy hok) w hw_norm hw_val'
  exact ⟨hres, by rw [hres, hsum_eq]; exact Rat.den_intCast _⟩

/-- **Exact integer subtraction.** -/
lemma operator_sub_exact_int (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxd : x.toRat.den = 1) (hyd : y.toRat.den = 1)
    (hbound : (x.toRat - y.toRat).num.natAbs < 2 ^ 63)
    (hok : Number.operator_sub x y .to_nearest = .ok result) :
    result.toRat = x.toRat - y.toRat ∧ result.toRat.den = 1 := by
  have hxq := toRat_eq_num_cast x hxd
  have hyq := toRat_eq_num_cast y hyd
  have hsum_eq : x.toRat - y.toRat = ((x.toRat.num - y.toRat.num : ℤ) : ℚ) := by
    conv_lhs => rw [hxq, hyq]
    push_cast; ring
  have hnum : (x.toRat - y.toRat).num = x.toRat.num - y.toRat.num := by
    rw [hsum_eq]; exact Rat.num_intCast _
  have hbound' : (x.toRat.num - y.toRat.num).natAbs < 2 ^ 63 := by rw [← hnum]; exact hbound
  obtain ⟨w, hw_norm, hw_val⟩ := Number.exists_normalized_of_int _ hbound'
  have hw_val' : w.toRat = x.toRat - y.toRat := by rw [hw_val, ← hsum_eq]
  have hres : result.toRat = x.toRat - y.toRat :=
    Number.RoundsToRepresentable.eq_of_representable result _
      (operator_sub_rounded_to_nearest x y result hx hy hok) w hw_norm hw_val'
  exact ⟨hres, by rw [hres, hsum_eq]; exact Rat.den_intCast _⟩

end XRPL.Model.Protocol
