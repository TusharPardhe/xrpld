import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.Common.AmountArith

/-! # Proof body for the `IntAmount.mulRatio` correctness headline.

`mulRatio amt num den roundUp` is the one `IntAmount` operation that **rounds**: it computes
`amt · num / den` with truncated integer division, nudges by `±1` to realize floor
(`roundUp = false`) or ceil (`roundUp = true`), and returns overflow outside the closed
`Int64` range. The unified correctness proof lives here; the
direction-specialized forms (the `roundUp` analog of `Number`'s per-mode split) are in
`MulRatio.Common.Floor.Proofs` / `MulRatio.Common.Ceil.Proofs`. The integer / rational
rounding brackets are the shared `AmountArith` lemmas. -/

namespace XRPL.Model.Protocol

/-- **`mulRatio` rounds correctly (floor for `roundUp = false`, ceil for `roundUp = true`).**
On a successful (`.ok`) result the drops are the correctly-rounded quotient of
`amt * num / den`; values outside the `Int64` range return overflow. -/
theorem IntAmount.mulRatio_rounds_proof (amt : IntAmount) (num den : UInt32) (roundUp : Bool)
    (result : IntAmount)
    (hok : IntAmount.mulRatio amt num den roundUp = .ok result) :
    result.value = Int64.minValue ∨
      (if roundUp
       then amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) ≤ result.toRat ∧
            result.toRat - 1 < amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ)
       else result.toRat ≤ amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) ∧
            amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) < result.toRat + 1) := by
  -- `den = 0` makes `mulRatio` error, contradicting `hok`; the real work is `den ≠ 0`.
  by_cases hden : den = 0
  · rw [show IntAmount.mulRatio amt num den roundUp = Except.error .divByZero from by
          unfold IntAmount.mulRatio; rw [if_pos (by simpa using hden)]] at hok
    exact absurd hok (by simp)
  set m : ℤ := amt.value.toInt * (num.toNat : ℤ) with hm_def
  set d : ℤ := (den.toNat : ℤ) with hd_def
  set R : ℤ := if m.tmod d ≠ 0 then
                 if (!decide (amt.value < 0) && roundUp) = true then m.tdiv d + 1
                 else if (decide (amt.value < 0) && !roundUp) = true then m.tdiv d - 1 else m.tdiv d
               else m.tdiv d with hR_def
  -- `d > 0`
  have hdnat : den.toNat ≠ 0 := by
    intro h; exact hden (by simpa using (UInt32.toNat_inj.mp (by simpa using h)))
  have hd : (0 : ℤ) < d := by rw [hd_def]; exact_mod_cast Nat.pos_of_ne_zero hdnat
  -- reduce the function call to a clean three-way if on `R`
  have key : IntAmount.mulRatio amt num den roundUp =
      (if R > Int64.maxValue.toInt then Except.error .overflow
       else if R < Int64.minValue.toInt then Except.error .overflow
       else Except.ok ⟨R.toInt64⟩) := by
    unfold IntAmount.mulRatio; rw [if_neg (by simpa using hden)]
  rw [key] at hok
  split_ifs at hok with hMax hMin
  · -- both out-of-range error cases are discharged by `split_ifs`; this is in-range success.
    right
    have hMax' : R ≤ Int64.maxValue.toInt := not_lt.mp hMax
    have hMin' : Int64.minValue.toInt ≤ R := not_lt.mp hMin
    have hresult : result = ⟨R.toInt64⟩ := (Except.ok.inj hok).symm
    have hround : (R.toInt64).toInt = R := AmountArith.toInt_toInt64_self hMin' hMax'
    have hrR : result.toRat = (R : ℚ) := by
      rw [hresult]; unfold IntAmount.toRat; rw [hround]
    have htruth : amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) = (m : ℚ) / (d : ℚ) := by
      rw [hm_def, hd_def]; unfold IntAmount.toRat; push_cast; ring
    -- sign bridge: relate the truncation flag `amt.value < 0` to the sign of `m`
    have hz : ((0 : Int64)).toInt = 0 := by decide
    have hlt0 : (amt.value < 0) ↔ amt.value.toInt < 0 := by
      rw [Int64.lt_iff_toInt_lt, hz]
    have hN : (0 : ℤ) ≤ (num.toNat : ℤ) := Int.natCast_nonneg _
    have hneg_lo : m < 0 → decide (amt.value < 0) = true := by
      intro hmlt
      have hD : amt.value.toInt < 0 := by rw [hm_def] at hmlt; nlinarith [hmlt, hN]
      exact decide_eq_true (hlt0.mpr hD)
    have hneg_hi : 0 < m → decide (amt.value < 0) = false := by
      intro hmgt
      have hD : 0 < amt.value.toInt := by rw [hm_def] at hmgt; nlinarith [hmgt, hN]
      exact decide_eq_false (by rw [hlt0]; omega)
    have hbrk := AmountArith.mulRatio_int_bracket m d R hd roundUp (decide (amt.value < 0))
      hneg_lo hneg_hi rfl
    rw [hrR, htruth]
    cases roundUp
    · simp only [Bool.false_eq_true, if_false] at hbrk ⊢
      exact AmountArith.rat_floor_bracket hd hbrk.1 hbrk.2
    · simp only [if_true] at hbrk ⊢
      exact AmountArith.rat_ceil_bracket hd hbrk.1 hbrk.2

end XRPL.Model.Protocol
