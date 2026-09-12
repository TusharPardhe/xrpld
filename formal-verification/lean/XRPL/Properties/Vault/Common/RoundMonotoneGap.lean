import XRPL.Properties.Protocol.Number.Common.Closest.Gap
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.GridPoint
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # Normalized minimal-relative-gap lemma

The novel arithmetic core resolving the cusp exact-tie in the vault monotonicity
proofs. Two distinct positive normalized `Number`s never sit closer than one
coarsest ULP apart in *relative* terms: `maxRep · (b − a) ≥ a`, i.e. the relative
gap is at least `1 / maxRep`. Since `1 / maxRep > 1 / (maxRep + ½) = 10^e / t` at
the cusp tie `t = (maxRep + ½)·10^e`, a larger normalized product jumps clear over
the sub-tie window, which defeats the (real) non-monotonicity of `doRoundUp` at the
cusp. -/

namespace XRPL.Model.Protocol

/-- Value of a positive `Number` as `mantissa · 10^exponent`. -/
lemma toRat_pos_val (n : Number) (hpos : 0 < n.toRat) :
    n.toRat = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ := by
  rw [← abs_of_pos hpos]; exact abs_toRat_eq n

/-- **Normalized minimal relative gap.** Two positive normalized numbers with
`a < b` satisfy `a ≤ maxRep · (b − a)`. Proof: `b` skips the open unit-cell above
`a`. When `a`'s mantissa `M ≤ maxRep`, the cell is `(M·10^E, (M+1)·10^E)`; when
`M > maxRep` (so `M % 10 = 0`), rescale one decade up and the cell is
`(M·10^E, (M+10)·10^E)`. In both cases `no_normalized_in_open_ulp_gap_pos_zm`
excludes `b`, forcing `b ≥` the cell top, whence the bound. -/
theorem normalized_gap_bound (a b : Number)
    (ha : a.isNormalized) (hb : b.isNormalized)
    (hapos : 0 < a.toRat) (hlt : a.toRat < b.toRat) :
    a.toRat ≤ (maxRepNat : ℚ) * (b.toRat - a.toRat) := by
  have hbpos : 0 < b.toRat := lt_trans hapos hlt
  have ha_ne : a.mantissa_ ≠ 0 := by
    intro h
    have : a.toRat = 0 := by
      rw [toRat_pos_val a hapos, show a.mantissa_.toNat = 0 from by rw [h]; rfl]; norm_num
    rw [this] at hapos; exact lt_irrefl 0 hapos
  have ha_val : a.toRat = (a.mantissa_.toNat : ℚ) * 10 ^ a.exponent_ := toRat_pos_val a hapos
  set MA : ℕ := a.mantissa_.toNat with hMA
  set EA : Int := a.exponent_ with hEA
  have hpow : (0 : ℚ) < 10 ^ EA := zpow_pos (by norm_num) _
  obtain ⟨hMlo, hMhi⟩ := ha.mantissaBounds_nat ha_ne
  have hMlt : (MA : ℚ) < (10 ^ 19 : ℚ) := by exact_mod_cast hMhi
  have hcusp : a.mantissa_ ≤ maxRep ∨ a.mantissa_.toNat % 10 = 0 := by
    rcases ha with h | h
    · rw [h] at ha_ne; exact absurd rfl ha_ne
    · exact h.2.2.1
  by_contra hcon
  push_neg at hcon
  rw [ha_val] at hcon  -- hcon : maxRepNat * (b.toRat - MA*10^EA) < MA*10^EA
  by_cases hle : MA ≤ maxRepNat
  · -- M ≤ maxRep: cell (M·10^E, (M+1)·10^E)
    have hM_le : (MA : ℚ) ≤ (maxRepNat : ℚ) := by exact_mod_cast hle
    have hb_hi : b.toRat < ((MA : ℚ) + 1) * 10 ^ EA := by
      nlinarith [hcon, mul_nonneg (show (0:ℚ) ≤ (maxRepNat : ℚ) - MA from by linarith)
        (le_of_lt hpow), hpow]
    have hb_lo : (MA : ℚ) * 10 ^ EA < b.toRat := by rw [← ha_val]; exact hlt
    exact no_normalized_in_open_ulp_gap_pos_zm EA MA (by omega) (by omega) b hb hbpos hb_lo hb_hi
  · -- M > maxRep so M % 10 = 0: rescale, cell (M·10^E, (M+10)·10^E)
    push_neg at hle  -- hle : maxRepNat < MA
    have hmod : MA % 10 = 0 := by
      rcases hcusp with h | h
      · exfalso; have := UInt64.le_iff_toNat_le.mp h; rw [maxRep_val] at this; omega
      · exact h
    set MB : ℕ := MA / 10 with hMB
    have hMBmul : MB * 10 = MA := by rw [hMB]; omega
    have ha_val2 : a.toRat = (MB : ℚ) * 10 ^ (EA + 1) := by
      rw [ha_val, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0) EA 1, zpow_one]
      rw [show (MA : ℚ) = (MB : ℚ) * 10 from by exact_mod_cast hMBmul.symm]; ring
    have hpow2 : (0 : ℚ) < 10 ^ (EA + 1) := zpow_pos (by norm_num) _
    have hMB_ge : mantissaFloorSucc ≤ MB := by rw [hMB]; omega
    have hMB_lt : MB < 10 ^ 19 := by rw [hMB]; omega
    have hM10 : ((MB : ℚ) + 1) * 10 ^ (EA + 1) = ((MA : ℚ) + 10) * 10 ^ EA := by
      rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0) EA 1, zpow_one,
          show (MA : ℚ) = (MB : ℚ) * 10 from by exact_mod_cast hMBmul.symm]; ring
    have hb_hi : b.toRat < ((MB : ℚ) + 1) * 10 ^ (EA + 1) := by
      rw [hM10]
      nlinarith [hcon, mul_nonneg (show (0:ℚ) ≤ 10 * (maxRepNat : ℚ) - MA from by
        nlinarith [hMlt]) (le_of_lt hpow), hpow]
    have hb_lo : (MB : ℚ) * 10 ^ (EA + 1) < b.toRat := by rw [← ha_val2]; exact hlt
    exact no_normalized_in_open_ulp_gap_pos_zm (EA + 1) MB hMB_ge hMB_lt b hb hbpos hb_lo hb_hi

end XRPL.Model.Protocol
