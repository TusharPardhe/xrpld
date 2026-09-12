import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.LawfulSupport

/-! # `Vault.burnShares` accuracy proofs

Proof bodies behind the accuracy headlines in `VaultBurn.lean`. Both statements
are exact, so this file has no error bounds and no witness theorems. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **Proof body of `canBurnShares_assets_exact`.** -/
theorem Vault.canBurnShares_assets_exact_proof (v : Vault) (sharesTotalAmount : STAmount)
    (hok : v.canBurnShares = .ok (.assets sharesTotalAmount))
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    sharesTotalAmount.toRat = (v.toExact.sharesTotal : ℚ) := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
  unfold Vault.canBurnShares at hok
  simp only [] at hok
  by_cases hg : (v.sharesTotal.mantissa_ == 0 ||
      (v.assetsTotal.mantissa_ != 0 || v.assetsAvailable.mantissa_ != 0)) = true
  · rw [if_pos hg, epure] at hok
    exact CanBurnSharesResult.noConfusion (Except.ok.inj hok)
  · rw [if_neg hg] at hok
    simp only [pure_bind] at hok
    obtain ⟨sta, hofn, hok⟩ := bind_ok_peel _ _ _ hok
    rw [epure] at hok
    have hsta : sta = sharesTotalAmount := CanBurnSharesResult.assets.inj (Except.ok.inj hok)
    obtain ⟨_, _, _, _, hval⟩ := STAmount.ofNumber_int64_shape v.sharesTotal .to_nearest sta
      v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg v.wf.sharesTotal_int hfit' hofn
    rw [← hsta, hval, ← hST]

/-- **Proof body of `burnShares_sharesTotal_exact`.** -/
theorem Vault.burnShares_sharesTotal_exact_proof (v : Vault) (sharesDestroyed : STAmount)
    (v' : Vault)
    (hok : v.burnShares sharesDestroyed = .ok v')
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ))
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    (v'.toExact.sharesTotal : ℚ) =
      (v.toExact.sharesTotal : ℚ) - sharesDestroyed.toRat := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hsd_nn : 0 ≤ sharesDestroyed.toRat := STAmount.toRat_nonneg_of sharesDestroyed hnn
  have hsd_den : sharesDestroyed.toRat.den = 1 :=
    STAmount.IntegralCanonical.den_eq_one sharesDestroyed hcanon
  -- the stored magnitude is small
  have hsz : sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hsd_val : sharesDestroyed.toRat = ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) := by
      rw [STAmount.IntegralCanonical.toRat_eq_signedDrops sharesDestroyed hcanon]
      unfold STAmount.signedDrops
      rw [show sharesDestroyed.mIsNegative = false from hnn]
      simp only [Bool.false_eq_true, if_false]
      norm_cast
    have h1 : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [← hsd_val]
      exact le_trans hle (le_trans hfit (by norm_num))
    exact_mod_cast h1
  obtain ⟨sdn, hsdn_ok, hsdn_val, hsdn_norm⟩ :=
    STAmount.toNumber_integral_small_exact sharesDestroyed .to_nearest hcanon hsz
  -- walk the burn
  unfold Vault.burnShares at hok
  simp only [] at hok
  obtain ⟨sdn', hsdn', hok⟩ := bind_ok_peel _ _ _ hok
  have hsdn'_eq : sdn' = sdn := by rw [hsdn_ok] at hsdn'; exact (Except.ok.inj hsdn').symm
  rw [hsdn'_eq] at hok
  obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
  -- the in-op `to_lawful` re-check pins `v'.toRawVault` to the updated record
  have hv' : v'.toRawVault = { v with sharesTotal := st' } := (RawVault.to_lawful_ok hok).1
  -- the subtraction is exact
  have hxq := rat_eq_num_cast_of_den_one v.sharesTotal.toRat v.wf.sharesTotal_int
  have hyq := rat_eq_num_cast_of_den_one sdn.toRat (by rw [hsdn_val]; exact hsd_den)
  have hdiff : v.sharesTotal.toRat - sdn.toRat
      = ((v.sharesTotal.toRat.num - sdn.toRat.num : ℤ) : ℚ) := by
    conv_lhs => rw [← hxq, ← hyq]
    push_cast; ring
  have hdiff_den : (v.sharesTotal.toRat - sdn.toRat).den = 1 := by
    rw [hdiff]; exact Rat.den_intCast _
  have hdiff_nn : 0 ≤ v.sharesTotal.toRat - sdn.toRat := by
    rw [hsdn_val]
    have : sharesDestroyed.toRat ≤ v.sharesTotal.toRat := by rw [← hST]; exact hle
    linarith
  have hdiff_le : v.sharesTotal.toRat - sdn.toRat ≤ 2 ^ 63 - 1 := by
    have h1 : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
    rw [hsdn_val]
    linarith
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal sdn st'
    v.wf.sharesTotal_norm hsdn_norm v.wf.sharesTotal_int
    (by rw [hsdn_val]; exact hsd_den)
    (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
  -- read the new stored total back
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
  have hproj : (v'.toExact.sharesTotal : ℚ) = ((st'.toRat.num.toNat : ℕ) : ℚ) := by
    rw [hv']; rfl
  rw [hproj, rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn, hst_val, hsdn_val, ← hST]

end XRPL.Model.SingleAssetVault
