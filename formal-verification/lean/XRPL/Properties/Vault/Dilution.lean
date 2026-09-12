import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DilutionProofs
import XRPL.Properties.Vault.Common.DilutionWitness
import XRPL.Properties.Vault.Unchanged
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Correction-aware vault dilution API

A source execution can price a raw exchange amount and then store a different,
posterior-clamped final amount.  The theorem names are retained for compatibility,
but each non-witness result now exposes `finalClampCorrection` (or the reachability
history's `accumulatedClampCorrection`) on the left-hand side.  Thus the correction
is observable rather than being hidden by an invalid raw-equals-final rewrite.
-/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Final-state-corrected non-dilution for a non-donation deposit. -/
theorem Vault.deposit_no_dilution (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hL : v.toExact.lossUnrealized = 0) (hcnz : r.amountDeposit'.isZero = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
  Vault.deposit_no_dilution_proof v amountDeposit r hcanon hpos hL hcnz hSsz hok herr

/-- Concrete witness that a deposit can strictly dilute before correction. -/
theorem Vault.deposit_dilution_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧ v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  deposit_dilution_witness

/-- Final-state-corrected non-dilution for a donation.  The final accepted deposit,
not a raw intermediate, determines both the state and the correction. -/
theorem Vault.deposit_donation_no_dilution (v : Vault) (amountDeposit : STAmount)
    (r : DepositResult) (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hint_dom : amountDeposit.integral = true →
      (v.numericType = .int64 ∨ v.numericType = .native) ∧
      amountDeposit.mNumericType = v.numericType ∧ v.assetsTotal.toRat.den = 1 ∧
      v.assetsAvailable.toRat.den = 1 ∧ v.toExact.assetsTotal + amountDeposit.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
  Vault.deposit_donation_no_dilution_proof v amountDeposit r hcanon hpos hint_dom hok herr

/-- Final-debit-corrected non-dilution for a non-loss-waiving withdrawal. -/
theorem Vault.withdraw_no_dilution (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult)
    (hL : v.toExact.lossUnrealized = 0) (hcnz : r.assets'.isZero = false)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hmargin : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hok : v.withdraw amount false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
  Vault.withdraw_no_dilution_proof v amount r hL hcnz hnn hc hSnt hmargin hSfit hok herr

/-- Concrete witness that a withdrawal can strictly dilute before correction. -/
theorem Vault.withdraw_dilution_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult),
      v.withdraw amount false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  withdraw_dilution_witness

/-- Final-recovery-corrected non-dilution for clawback, including the zero-assets
claw-all route.  Raw recovery remains distinct from the posterior-clamped recovery. -/
theorem Vault.clawback_no_dilution (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hL : v.toExact.lossUnrealized = 0) (hc : assets.Canonical)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hmargin : r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
  Vault.clawback_no_dilution_proof v assets holderShares r hL hc hSic hSc hSnn hmargin hSfit hok herr

/-- Concrete witness that a nonzero clawback can strictly dilute before correction. -/
theorem Vault.clawback_dilution_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  clawback_dilution_witness

/-- Concrete witness for the zero-assets claw-all route. -/
theorem Vault.clawback_zero_dilution_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      assets.isZero = true ∧ holderShares.IntegralCanonical ∧ holderShares.Canonical ∧
      holderShares.negative = false ∧ v.clawback assets holderShares = .ok r ∧
      r.error = none ∧ r.sharesDestroyed = holderShares ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  clawback_zero_dilution_witness

/-- Corrected reachability theorem.  `h.accumulatedClampCorrection` is the explicit
invariant needed to account for final clamps at every completed step. -/
theorem Vault.ReachableFromIn.no_dilution (v : Vault) (n : ℕ) (w : Vault)
    (hwL : v.toExact.lossUnrealized = 0) (hwAV : v.assetsAvailable = v.assetsTotal)
    (h : Vault.ReachableFromIn v w n) :
    w.withdrawNav * (v.toExact.sharesTotal : ℚ) + h.accumulatedClampCorrection ≥
      v.withdrawNav * (w.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n :=
  Vault.ReachableFromIn.no_dilution_proof v n w hwL hwAV h

/-- Concrete two-step witness that uncorrected dilution is attained. -/
theorem Vault.ReachableFromIn.dilution_attained :
    ∃ (lw u : Vault) (n : ℕ), 1 < n ∧ Vault.ReachableFromIn lw u n ∧
      u.withdrawNav * (lw.toExact.sharesTotal : ℚ) <
        lw.withdrawNav * (u.toExact.sharesTotal : ℚ) :=
  dilution_attained_witness

end XRPL.Model.SingleAssetVault
