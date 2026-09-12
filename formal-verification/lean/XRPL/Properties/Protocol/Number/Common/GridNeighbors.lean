import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # 16-digit grid neighbors as normalized `Number`s

The 16-digit grid embeds in the 19-digit `Number` grid, so the points one 16-digit
ULP below/above a value `Mr·10^ec` are themselves normalized `Number`s. That makes
them admissible witnesses for the `Number.lower`/`upper` tightness lemmas, which
quantify over normalized `Number`s only: if a double-rounded result were more than
one ULP from the target, its far-side neighbor would be a representable value
between the correctly-rounded `Number` and the target — contradicting tightness.
Shared by the `Mul` and `Add` `DirectedTight` proofs. -/

namespace XRPL.Model.Protocol

/-- `(Mr − 1)·10^ec` is a non-negative normalized `Number`. -/
lemma exists_normalized_grid_below (Mr : ℕ) (ec : ℤ)
    (hlo : 10 ^ 15 ≤ Mr) (hhi : Mr < 10 ^ 16)
    (hec_lo : minExponent + 4 ≤ ec) (hec_hi : ec + 3 ≤ maxExponent) :
    ∃ m : Number, m.isNormalized ∧ m.negative_ = false ∧
      m.toRat = ((Mr : ℚ) - 1) * (10 : ℚ) ^ ec := by
  have hlgmin : largeRange.min.toNat = 10 ^ 18 := by decide
  have hlgmax : largeRange.max.toNat = 10 ^ 19 - 1 := by decide
  by_cases hM : Mr = 10 ^ 15
  · -- bottom of the mantissa range: represent at exponent `ec-4`, mantissa `(10¹⁵-1)·10⁴`.
    set k : ℕ := (Mr - 1) * 10000 with hk_def
    have hk_val : k = 10 ^ 19 - 10 ^ 4 := by rw [hk_def, hM]; norm_num
    have hk_lt : k < UInt64.size := by rw [uint64_size_val, hk_val]; omega
    have hk_toNat : (Nat.toUInt64 k).toNat = k := UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hk_lt)
    refine ⟨⟨false, Nat.toUInt64 k, ec - 4⟩, ?_, rfl, ?_⟩
    · right
      refine ⟨?_, ?_, Or.inr ?_, (by show minExponent ≤ ec - 4; omega),
        (by show ec - 4 ≤ maxExponent; omega)⟩
      · rw [UInt64.le_iff_toNat_le, hlgmin, hk_toNat, hk_val]; omega
      · rw [UInt64.le_iff_toNat_le, hlgmax, hk_toNat, hk_val]; omega
      · rw [hk_toNat, hk_val]; omega
    · rw [Number.toRat_of_nonneg _ rfl]
      show ((Nat.toUInt64 k).toNat : ℚ) * (10 : ℚ) ^ (ec - 4) = ((Mr : ℚ) - 1) * (10 : ℚ) ^ ec
      rw [hk_toNat, hk_def, hM]
      have hpow : (10 : ℚ) ^ ec = (10 : ℚ) ^ (ec - 4) * 10000 := by
        rw [show ec = (ec - 4) + 4 by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0) (ec - 4) 4]
        push_cast; norm_num
      rw [hpow]; push_cast; ring
  · -- generic: represent at exponent `ec-3`, mantissa `(Mr-1)·1000`.
    set k : ℕ := (Mr - 1) * 1000 with hk_def
    have hMr1 : 10 ^ 15 < Mr := by omega
    have hk_lo : 10 ^ 18 ≤ k := by rw [hk_def]; omega
    have hk_hi : k < 10 ^ 19 := by rw [hk_def]; omega
    have hk_lt : k < UInt64.size := by rw [uint64_size_val]; omega
    have hk_toNat : (Nat.toUInt64 k).toNat = k := UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hk_lt)
    refine ⟨⟨false, Nat.toUInt64 k, ec - 3⟩, ?_, rfl, ?_⟩
    · right
      refine ⟨?_, ?_, Or.inr ?_, (by show minExponent ≤ ec - 3; omega),
        (by show ec - 3 ≤ maxExponent; omega)⟩
      · rw [UInt64.le_iff_toNat_le, hlgmin, hk_toNat]; omega
      · rw [UInt64.le_iff_toNat_le, hlgmax, hk_toNat]; omega
      · rw [hk_toNat, hk_def]; omega
    · rw [Number.toRat_of_nonneg _ rfl]
      show ((Nat.toUInt64 k).toNat : ℚ) * (10 : ℚ) ^ (ec - 3) = ((Mr : ℚ) - 1) * (10 : ℚ) ^ ec
      rw [hk_toNat, hk_def]
      have hpow : (10 : ℚ) ^ ec = (10 : ℚ) ^ (ec - 3) * 1000 := by
        rw [show ec = (ec - 3) + 3 by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0) (ec - 3) 3]
        push_cast; norm_num
      rw [hpow]
      have hcast : (((Mr - 1) * 1000 : ℕ) : ℚ) = ((Mr : ℚ) - 1) * 1000 := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]; ring

/-- `(Mr + 1)·10^ec` is a non-negative normalized `Number`. -/
lemma exists_normalized_grid_above (Mr : ℕ) (ec : ℤ)
    (hlo : 10 ^ 15 ≤ Mr) (hhi : Mr < 10 ^ 16)
    (hec_lo : minExponent + 4 ≤ ec) (hec_hi : ec + 3 ≤ maxExponent) :
    ∃ m : Number, m.isNormalized ∧ m.negative_ = false ∧
      m.toRat = ((Mr : ℚ) + 1) * (10 : ℚ) ^ ec := by
  have hlgmin : largeRange.min.toNat = 10 ^ 18 := by decide
  have hlgmax : largeRange.max.toNat = 10 ^ 19 - 1 := by decide
  by_cases hM : Mr + 1 = 10 ^ 16
  · -- top of the mantissa range: represent at exponent `ec-2`, mantissa `10¹⁸`.
    set k : ℕ := 10 ^ 18 with hk_def
    have hk_lt : k < UInt64.size := by rw [uint64_size_val, hk_def]; omega
    have hk_toNat : (Nat.toUInt64 k).toNat = k := UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hk_lt)
    refine ⟨⟨false, Nat.toUInt64 k, ec - 2⟩, ?_, rfl, ?_⟩
    · right
      refine ⟨?_, ?_, Or.inr ?_, (by show minExponent ≤ ec - 2; omega),
        (by show ec - 2 ≤ maxExponent; omega)⟩
      · rw [UInt64.le_iff_toNat_le, hlgmin, hk_toNat, hk_def]
      · rw [UInt64.le_iff_toNat_le, hlgmax, hk_toNat, hk_def]; omega
      · rw [hk_toNat, hk_def]; omega
    · rw [Number.toRat_of_nonneg _ rfl]
      show ((Nat.toUInt64 k).toNat : ℚ) * (10 : ℚ) ^ (ec - 2) = ((Mr : ℚ) + 1) * (10 : ℚ) ^ ec
      rw [hk_toNat, hk_def]
      have hMq : (Mr : ℚ) + 1 = (10 : ℚ) ^ 16 := by exact_mod_cast hM
      rw [hMq]
      have hpow : (10 : ℚ) ^ ec = (10 : ℚ) ^ (ec - 2) * 100 := by
        rw [show ec = (ec - 2) + 2 by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0) (ec - 2) 2]
        push_cast; norm_num
      rw [hpow]; push_cast; ring
  · -- generic: represent at exponent `ec-3`, mantissa `(Mr+1)·1000`.
    set k : ℕ := (Mr + 1) * 1000 with hk_def
    have hMr1 : Mr + 1 < 10 ^ 16 := by omega
    have hk_lo : 10 ^ 18 ≤ k := by rw [hk_def]; omega
    have hk_hi : k < 10 ^ 19 := by rw [hk_def]; omega
    have hk_lt : k < UInt64.size := by rw [uint64_size_val]; omega
    have hk_toNat : (Nat.toUInt64 k).toNat = k := UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hk_lt)
    refine ⟨⟨false, Nat.toUInt64 k, ec - 3⟩, ?_, rfl, ?_⟩
    · right
      refine ⟨?_, ?_, Or.inr ?_, (by show minExponent ≤ ec - 3; omega),
        (by show ec - 3 ≤ maxExponent; omega)⟩
      · rw [UInt64.le_iff_toNat_le, hlgmin, hk_toNat]; omega
      · rw [UInt64.le_iff_toNat_le, hlgmax, hk_toNat]; omega
      · rw [hk_toNat, hk_def]; omega
    · rw [Number.toRat_of_nonneg _ rfl]
      show ((Nat.toUInt64 k).toNat : ℚ) * (10 : ℚ) ^ (ec - 3) = ((Mr : ℚ) + 1) * (10 : ℚ) ^ ec
      rw [hk_toNat, hk_def]
      have hpow : (10 : ℚ) ^ ec = (10 : ℚ) ^ (ec - 3) * 1000 := by
        rw [show ec = (ec - 3) + 3 by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0) (ec - 3) 3]
        push_cast; norm_num
      rw [hpow]
      have hcast : (((Mr + 1) * 1000 : ℕ) : ℚ) = ((Mr : ℚ) + 1) * 1000 := by push_cast; ring
      rw [hcast]; ring

/-- Flip the sign bit of a positive normalized `Number`: it stays normalized and its
rational value negates. Shared tail of the two `_neg` grid-neighbor lemmas. -/
private lemma exists_grid_neg_of {m0 : Number} {t : ℚ} (hnorm : m0.isNormalized)
    (hneg0 : m0.negative_ = false) (hval : m0.toRat = t) (ht : 0 < t) :
    ∃ m : Number, m.isNormalized ∧ m.negative_ = true ∧ m.toRat = -t := by
  refine ⟨⟨true, m0.mantissa_, m0.exponent_⟩, ?_, rfl, ?_⟩
  · rcases hnorm with hz | hfields
    · rw [hz, Number.toRat_zero] at hval
      exact absurd hval.symm ht.ne'
    · exact Or.inr hfields
  · rw [Number.toRat_of_neg _ rfl]
    exact congrArg Neg.neg ((Number.toRat_of_nonneg m0 hneg0).symm.trans hval)

/-- `-((Mr − 1)·10^ec)` is a negative normalized `Number`. -/
lemma exists_normalized_grid_below_neg (Mr : ℕ) (ec : ℤ)
    (hlo : 10 ^ 15 ≤ Mr) (hhi : Mr < 10 ^ 16)
    (hec_lo : minExponent + 4 ≤ ec) (hec_hi : ec + 3 ≤ maxExponent) :
    ∃ m : Number, m.isNormalized ∧ m.negative_ = true ∧
      m.toRat = -(((Mr : ℚ) - 1) * (10 : ℚ) ^ ec) := by
  obtain ⟨m0, hnorm, hneg0, hval⟩ := exists_normalized_grid_below Mr ec hlo hhi hec_lo hec_hi
  have hMr1 : (0 : ℚ) < (Mr : ℚ) - 1 := by
    have : (1 : ℚ) < (Mr : ℚ) := by exact_mod_cast (show (1 : ℕ) < Mr by omega)
    linarith
  exact exists_grid_neg_of hnorm hneg0 hval (mul_pos hMr1 (zpow_pos (by norm_num) _))

/-- `-((Mr + 1)·10^ec)` is a negative normalized `Number`. -/
lemma exists_normalized_grid_above_neg (Mr : ℕ) (ec : ℤ)
    (hlo : 10 ^ 15 ≤ Mr) (hhi : Mr < 10 ^ 16)
    (hec_lo : minExponent + 4 ≤ ec) (hec_hi : ec + 3 ≤ maxExponent) :
    ∃ m : Number, m.isNormalized ∧ m.negative_ = true ∧
      m.toRat = -(((Mr : ℚ) + 1) * (10 : ℚ) ^ ec) := by
  obtain ⟨m0, hnorm, hneg0, hval⟩ := exists_normalized_grid_above Mr ec hlo hhi hec_lo hec_hi
  exact exists_grid_neg_of hnorm hneg0 hval (by positivity)

end XRPL.Model.Protocol
