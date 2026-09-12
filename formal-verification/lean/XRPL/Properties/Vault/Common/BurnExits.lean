import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Vault.Common.Reduction

/-! # `Vault.burnShares` exit reductions

Proof bodies behind the exit headlines in `VaultBurnReturn.lean`. Each walk uses
`bind_ok_peel`, `if`-elimination, and the boolean guard lemmas only, keeping the
`ofNumber`/`operator_sub` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **Proof body of `canBurnShares_rejected_code`.** -/
theorem Vault.canBurnShares_rejected_code_proof (v : Vault) (ter : TER)
    (hok : v.canBurnShares = .ok (.error ter)) :
    ter = .tecNO_PERMISSION := by
  unfold Vault.canBurnShares at hok
  simp only [] at hok
  by_cases hg : (v.sharesTotal.mantissa_ == 0 ||
      (v.assetsTotal.mantissa_ != 0 || v.assetsAvailable.mantissa_ != 0)) = true
  · rw [if_pos hg] at hok
    injection hok with h
    exact (CanBurnSharesResult.error.inj h).symm
  · rw [if_neg hg] at hok
    simp only [pure_bind] at hok
    obtain ⟨a, _, hok⟩ := bind_ok_peel _ _ _ hok
    injection hok with h
    injection h

/-- **Proof body of `canBurnShares_no_permission`.** Force-burning shares is
allowed only when shares are outstanding while both asset totals are zero. When
`sharesTotal` is zero, or `assetsTotal` or `assetsAvailable` is nonzero:
`.error .tecNO_PERMISSION`. -/
theorem Vault.canBurnShares_no_permission_proof (v : Vault)
    (hperm : v.sharesTotal.mantissa_ = 0 ∨
      v.assetsTotal.mantissa_ ≠ 0 ∨ v.assetsAvailable.mantissa_ ≠ 0) :
    v.canBurnShares = .ok (.error .tecNO_PERMISSION) := by
  have hguard : (v.sharesTotal.mantissa_ == 0 ||
      (v.assetsTotal.mantissa_ != 0 || v.assetsAvailable.mantissa_ != 0)) = true := by
    rcases hperm with h | h | h
    · rw [beq_iff_eq.mpr h, Bool.true_or]
    · rw [bne_iff_ne.mpr h, Bool.true_or, Bool.or_true]
    · rw [bne_iff_ne.mpr h, Bool.or_true, Bool.or_true]
  unfold Vault.canBurnShares
  simp only []
  rw [if_pos hguard]
  rfl

/-- **Proof body of `canBurnShares_ok`.** The vault has outstanding shares and
both `assetsTotal` and `assetsAvailable` are zero: the result is the whole
`sharesTotal` converted to an `int64` amount. -/
theorem Vault.canBurnShares_ok_proof (v : Vault) (sharesTotalAmount : STAmount)
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (hat : v.assetsTotal.mantissa_ = 0)
    (hav : v.assetsAvailable.mantissa_ = 0)
    (hshares : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    v.canBurnShares = .ok (.assets sharesTotalAmount) := by
  have hguard : (v.sharesTotal.mantissa_ == 0 ||
      (v.assetsTotal.mantissa_ != 0 || v.assetsAvailable.mantissa_ != 0)) = false := by
    rw [beq_eq_false_iff_ne.mpr hsh, bne_eq_false_iff_eq.mpr hat,
      bne_eq_false_iff_eq.mpr hav, Bool.false_or, Bool.false_or]
  unfold Vault.canBurnShares
  simp only []
  rw [if_neg (by rw [hguard]; exact Bool.false_ne_true)]
  rw [hshares, ok_bind]
  rfl

end XRPL.Model.SingleAssetVault
