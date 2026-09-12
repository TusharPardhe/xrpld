import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Signum.Signum

/-! # Lawful-state query characterizations (proofs) -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a lawful state, `isInsolvent` holds exactly when the vault has no assets
but shares outstanding. -/
theorem Vault.isInsolvent_iff_proof (v : Vault) :
    v.isInsolvent = true ↔ v.toExact.assetsTotal = 0 ∧ 0 < v.toExact.sharesTotal := by
  unfold Vault.isInsolvent
  unfold RawVault.toExact
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Number.toRat_eq_zero_iff.symm, signum_eq_one_iff v.sharesTotal v.wf.sharesTotal_norm]
  have hcast : ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    have : (0:ℚ) < ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ) := by rw [hcast]; exact hs
    exact_mod_cast this
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    have : (0:ℚ) < ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ) := by exact_mod_cast hs
    rw [hcast] at this; exact this

end XRPL.Model.SingleAssetVault
