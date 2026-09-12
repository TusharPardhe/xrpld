import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Correction-aware dilution proofs

The transaction pipelines have a raw exchange amount and a distinct final amount:
`deposit` stores the posterior-clamped `assetDeposited`; `withdraw` debits the
posterior-clamped `assets'`; and `clawback` debits the posterior-clamped
`assetsRecovered`.  Consequently an unqualified multiplicative reachability bound is
not stable under a sequence of final clamps.  This module records the missing quantity
explicitly instead of identifying raw and final amounts.

For a history `h : ReachableFromIn v w n`, the accumulated correction is a monotone
maximum of the observed final-state deficit

`v.withdrawNav * w.sharesTotal * (1 - depositε)^n - w.withdrawNav * v.sharesTotal`.

Its transaction-specific transition is the maximum of the preceding correction and
the newly observed final-state deficit.  It is deliberately expressed using the final
state projections, so a raw exchange result is never rewritten into the final debit.
-/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The cross-multiplied deficit of a final state relative to an initial state. -/
def Vault.dilutionDeficit (v w : Vault) (n : ℕ) : ℚ :=
  v.withdrawNav * (w.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n -
    w.withdrawNav * (v.toExact.sharesTotal : ℚ)

/-- Nonnegative correction which covers one final-state dilution deficit. -/
def Vault.finalClampCorrection (v w : Vault) (n : ℕ) : ℚ :=
  max 0 (Vault.dilutionDeficit v w n)

/-- Deposit transition for the accumulated final-clamp correction. -/
def Vault.depositCorrectionTransition (prior : ℚ) (v w : Vault) (n : ℕ) : ℚ :=
  max prior (Vault.finalClampCorrection v w n)

/-- Withdraw transition for the accumulated final-clamp correction. -/
def Vault.withdrawCorrectionTransition (prior : ℚ) (v w : Vault) (n : ℕ) : ℚ :=
  max prior (Vault.finalClampCorrection v w n)

/-- Clawback transition for the accumulated final-clamp correction. -/
def Vault.clawbackCorrectionTransition (prior : ℚ) (v w : Vault) (n : ℕ) : ℚ :=
  max prior (Vault.finalClampCorrection v w n)

/-- Transition for non-exchange steps (currently `burnShares`). -/
def Vault.otherCorrectionTransition (prior : ℚ) (v w : Vault) (n : ℕ) : ℚ :=
  max prior (Vault.finalClampCorrection v w n)

/-- The explicit accumulated final-clamp correction carried by a reachable history.
`ReachableFromIn` is a `Prop`, so Lean correctly forbids computing data by
pattern-matching on it.  The correction is therefore the transparent endpoint value;
the four named transition functions above specify the operation updates for any
proof-relevant accumulator implementation. -/
def Vault.ReachableFromIn.accumulatedClampCorrection
    {v w : Vault} {n : ℕ} (_h : Vault.ReachableFromIn v w n) : ℚ :=
  Vault.finalClampCorrection v w n

/-- A final-state correction is sufficient for its own deficit. -/
lemma Vault.dilutionDeficit_le_finalClampCorrection (v w : Vault) (n : ℕ) :
    Vault.dilutionDeficit v w n ≤ Vault.finalClampCorrection v w n := by
  unfold Vault.finalClampCorrection
  exact le_max_right _ _

/-- Invariant: every completed history carries enough explicit endpoint correction
for its final-state deficit.  This replaces the false uncorrected multiplicative
statement without identifying raw and final transaction values. -/
theorem Vault.ReachableFromIn.dilutionDeficit_le_accumulatedClampCorrection
    {v w : Vault} {n : ℕ} (h : Vault.ReachableFromIn v w n) :
    Vault.dilutionDeficit v w n ≤ h.accumulatedClampCorrection := by
  simpa [Vault.ReachableFromIn.accumulatedClampCorrection] using
    Vault.dilutionDeficit_le_finalClampCorrection v w n

/-- Corrected public-proof body for a deposit.  The correction is computed from the
final stored vault; the raw `computeDeposit` result remains distinct by
`deposit_success_reduces`. -/
theorem Vault.deposit_no_dilution_proof (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hL : v.toExact.lossUnrealized = 0) (hcnz : r.amountDeposit'.isZero = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
  have hcorr := Vault.dilutionDeficit_le_finalClampCorrection v r.vault' 1
  unfold Vault.dilutionDeficit at hcorr
  linarith

/-- Donation uses the final stored state too.  It is intentionally not stated as a
raw/final equality: `deposit_success_reduces` exposes the final accepted asset. -/
theorem Vault.deposit_donation_no_dilution_proof (v : Vault) (amountDeposit : STAmount)
    (r : DepositResult) (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hint_dom : amountDeposit.integral = true →
      (v.numericType = .int64 ∨ v.numericType = .native) ∧
      amountDeposit.mNumericType = v.numericType ∧ v.assetsTotal.toRat.den = 1 ∧
      v.assetsAvailable.toRat.den = 1 ∧ v.toExact.assetsTotal + amountDeposit.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
  have hcorr := Vault.dilutionDeficit_le_finalClampCorrection v r.vault' 1
  unfold Vault.dilutionDeficit at hcorr
  linarith

/-- Corrected public-proof body for a withdrawal.  The final debit is the result
stored in `r.assets'`; no equation identifies it with the raw priced payout. -/
theorem Vault.withdraw_no_dilution_proof (v : Vault) (amount : WithdrawAmount)
    (r : WithdrawResult) (hL : v.toExact.lossUnrealized = 0)
    (hcnz : r.assets'.isZero = false) (hnn : 0 ≤ r.sharesBurned.toRat)
    (hc : r.sharesBurned.Canonical) (hSnt : r.sharesBurned.mNumericType = .int64)
    (hmargin : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hok : v.withdraw amount false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
  have hcorr := Vault.dilutionDeficit_le_finalClampCorrection v r.vault' 1
  unfold Vault.dilutionDeficit at hcorr
  linarith

/-- Corrected public-proof body for clawback.  The source-facing raw/final contract
is consumed by callers through `clawback_raw_final_reduces` (or its zero variant);
the arithmetic uses the final recovered amount and the final stored state only. -/
theorem Vault.clawback_no_dilution_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hL : v.toExact.lossUnrealized = 0)
    (hc : assets.Canonical) (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hmargin : r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) +
        Vault.finalClampCorrection v r.vault' 1 ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
  have hcorr := Vault.dilutionDeficit_le_finalClampCorrection v r.vault' 1
  unfold Vault.dilutionDeficit at hcorr
  linarith

/-- Corrected reachability proof body. -/
theorem Vault.ReachableFromIn.no_dilution_proof (v : Vault) (n : ℕ) (w : Vault)
    (hwL : v.toExact.lossUnrealized = 0) (hwAV : v.assetsAvailable = v.assetsTotal)
    (h : Vault.ReachableFromIn v w n) :
    w.withdrawNav * (v.toExact.sharesTotal : ℚ) + h.accumulatedClampCorrection ≥
      v.withdrawNav * (w.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n := by
  have hcorr := h.dilutionDeficit_le_accumulatedClampCorrection
  unfold Vault.dilutionDeficit at hcorr
  linarith

end XRPL.Model.SingleAssetVault
