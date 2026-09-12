import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Model.Vault.VaultSet
import XRPL.Model.Vault.VaultDelete

/-! # Shared bridges for the pure vault guards

`canVaultSet` and `canVaultDelete` are boolean guards over `Number.operator_ne` /
`Number.operator_lt`. Their exit theorems need two bridges:

* a structural one, `operator_eq`/`operator_ne` decide record equality of the
  three `Number` fields, used where the statement compares against `Number.zero`
  with `=`/`≠`;
* the rational one from `Compare`, `operator_ne`/`operator_lt` agree with the
  order on `toRat` once both sides are normalized.
-/

namespace XRPL.Model.Protocol

/-- `Number.operator_eq` decides structural record equality. -/
theorem Number.operator_eq_iff_eq (x y : Number) :
    x.operator_eq y = true ↔ x = y := by
  unfold Number.operator_eq
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨hn, hm⟩, he⟩
    obtain ⟨xn, xm, xe⟩ := x
    obtain ⟨yn, ym, ye⟩ := y
    simp only at hn hm he
    subst hn; subst hm; subst he; rfl
  · rintro rfl
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- `Number.operator_ne` decides structural record inequality. -/
theorem Number.operator_ne_iff_ne (x y : Number) :
    x.operator_ne y = true ↔ x ≠ y := by
  rw [ne_eq, ← Number.operator_eq_iff_eq]
  unfold Number.operator_ne
  cases x.operator_eq y <;> simp

/-- `Number.zero` is normalized. -/
theorem Number.zero_isNormalized : Number.zero.isNormalized := Or.inl rfl

/-- On a normalized number, `operator_ne` against zero is false exactly at
rational zero. -/
theorem Number.operator_ne_zero_eq_false_iff (x : Number) (hx : x.isNormalized) :
    x.operator_ne Number.zero = false ↔ x.toRat = 0 := by
  rw [Bool.eq_false_iff, ne_eq, operator_ne_iff x Number.zero hx Number.zero_isNormalized,
      Number.toRat_zero, not_not]

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `Vault.canVaultSet` proof bodies -/

/-- **Proof body of `canVaultSet_below_total`.** -/
theorem Vault.canVaultSet_below_total_proof (v : Vault) (assetsMaximum : Number)
    (hne : assetsMaximum.operator_ne Number.zero = true)
    (hlt : assetsMaximum.operator_lt v.assetsTotal = true) :
    v.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED := by
  unfold Vault.canVaultSet
  exact if_pos (by rw [Bool.and_eq_true]; exact ⟨hne, hlt⟩)

/-- **Proof body of `canVaultSet_success`.** -/
theorem Vault.canVaultSet_success_proof (v : Vault) (assetsMaximum : Number)
    (hok : (assetsMaximum.operator_ne Number.zero &&
        assetsMaximum.operator_lt v.assetsTotal) = false) :
    v.canVaultSet assetsMaximum = .tesSUCCESS := by
  unfold Vault.canVaultSet
  exact if_neg (by rw [Bool.not_eq_true]; exact hok)

/-- **Proof body of `canVaultSet_error_codes`.** -/
theorem Vault.canVaultSet_error_codes_proof (v : Vault) (assetsMaximum : Number) :
    v.canVaultSet assetsMaximum = .tesSUCCESS ∨
    v.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED := by
  unfold Vault.canVaultSet
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **Proof body of `lawful_canVaultSet_iff`.** -/
theorem Vault.lawful_canVaultSet_iff_proof (v : Vault)
    (assetsMaximum : Number)
    (hnorm : assetsMaximum.isNormalized) :
    v.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ v.toExact.assetsTotal ≤ assetsMaximum.toRat := by
  have htotal : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  -- the nonzero guard vanishes exactly at rational zero
  have hb1 : assetsMaximum.operator_ne Number.zero = false ↔ assetsMaximum.toRat = 0 :=
    Number.operator_ne_zero_eq_false_iff assetsMaximum hnorm
  -- the below-total guard vanishes exactly when the maximum is at least the total
  have hb2 : assetsMaximum.operator_lt v.assetsTotal = false ↔
      v.assetsTotal.toRat ≤ assetsMaximum.toRat := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff assetsMaximum v.assetsTotal hnorm htotal, not_lt]
  -- `v.toExact.assetsTotal` is `v.assetsTotal.toRat` by definition of `toExact`
  show v.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ v.assetsTotal.toRat ≤ assetsMaximum.toRat
  unfold Vault.canVaultSet
  by_cases hc : (assetsMaximum.operator_ne Number.zero &&
      assetsMaximum.operator_lt v.assetsTotal) = true
  · rw [if_pos hc]
    rw [Bool.and_eq_true] at hc
    refine iff_of_false (by decide) ?_
    rintro (h0 | hle)
    · rw [hb1.mpr h0] at hc; exact absurd hc.1 (by decide)
    · rw [hb2.mpr hle] at hc; exact absurd hc.2 (by decide)
  · rw [if_neg hc]
    rw [Bool.not_eq_true, Bool.and_eq_false_iff] at hc
    refine iff_of_true rfl ?_
    rcases hc with h1 | h2
    · exact Or.inl (hb1.mp h1)
    · exact Or.inr (hb2.mp h2)

/-! ## `Vault.canVaultDelete` proof bodies -/

/-- **Proof body of `lawful_canVaultDelete_iff`.** On a lawful vault
`assetsAvailable ≤ assetsTotal` and `0 ≤ assetsAvailable`, so `assetsTotal = 0`
already forces `assetsAvailable = 0`. The redundant middle conjunct is dropped:
the success condition is `assetsTotal = 0 ∧ sharesTotal = 0`, and the
`assetsAvailable` guard (checked first) is discharged from `assetsTotal = 0`. -/
theorem Vault.lawful_canVaultDelete_iff_proof (v : Vault) :
    v.canVaultDelete = .tesSUCCESS ↔
      v.toExact.assetsTotal = 0 ∧ v.toExact.sharesTotal = 0 := by
  have hav := Number.operator_ne_zero_eq_false_iff v.assetsAvailable v.wf.assetsAvailable_norm
  have hat := Number.operator_ne_zero_eq_false_iff v.assetsTotal v.wf.assetsTotal_norm
  have hst := Number.operator_ne_zero_eq_false_iff v.sharesTotal v.wf.sharesTotal_norm
  have hshares : v.toExact.sharesTotal = 0 ↔ v.sharesTotal.toRat = 0 := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, Nat.cast_eq_zero]
  -- on a lawful vault `assetsTotal = 0` forces `assetsAvailable = 0`
  have hAV0 : v.assetsTotal.toRat = 0 → v.assetsAvailable.toRat = 0 := fun h => by
    have hle : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
    have hnn : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
    rw [h] at hle
    exact le_antisymm hle hnn
  show v.canVaultDelete = .tesSUCCESS ↔
      v.assetsTotal.toRat = 0 ∧ v.toExact.sharesTotal = 0
  rw [← hat, hshares, ← hst]
  unfold Vault.canVaultDelete
  split_ifs with h1 h2 h3
  · refine iff_of_false (by decide) ?_
    rintro ⟨hat', _⟩
    have hAvz : v.assetsAvailable.operator_ne Number.zero = false := hav.mpr (hAV0 (hat.mp hat'))
    rw [hAvz] at h1; exact absurd h1 (by decide)
  · refine iff_of_false (by decide) ?_
    rintro ⟨hat', _⟩; rw [h2] at hat'; exact absurd hat' (by decide)
  · refine iff_of_false (by decide) ?_
    rintro ⟨_, hst'⟩; rw [h3] at hst'; exact absurd hst' (by decide)
  · exact iff_of_true rfl ⟨Bool.eq_false_iff.mpr h2, Bool.eq_false_iff.mpr h3⟩

/-- **Proof body of `canVaultDelete_error_codes`.** -/
theorem Vault.canVaultDelete_error_codes_proof (v : Vault) :
    v.canVaultDelete = .tesSUCCESS ∨
    v.canVaultDelete = .tecHAS_OBLIGATIONS := by
  unfold Vault.canVaultDelete
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **Proof body of `canVaultDelete_has_obligations_iff`.** -/
theorem Vault.canVaultDelete_has_obligations_iff_proof (v : Vault) :
    v.canVaultDelete = .tecHAS_OBLIGATIONS ↔
      (v.assetsAvailable ≠ Number.zero ∨ v.assetsTotal ≠ Number.zero ∨
        v.sharesTotal ≠ Number.zero) := by
  unfold Vault.canVaultDelete
  rw [← Number.operator_ne_iff_ne v.assetsAvailable, ← Number.operator_ne_iff_ne v.assetsTotal,
      ← Number.operator_ne_iff_ne v.sharesTotal]
  split_ifs with h1 h2 h3
  · exact iff_of_true rfl (Or.inl h1)
  · exact iff_of_true rfl (Or.inr (Or.inl h2))
  · exact iff_of_true rfl (Or.inr (Or.inr h3))
  · refine iff_of_false (by decide) ?_
    rintro (h | h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h

end XRPL.Model.SingleAssetVault
