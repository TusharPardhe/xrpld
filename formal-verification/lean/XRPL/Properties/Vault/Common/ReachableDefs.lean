import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.Create
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback

/-! # Reachability inductives

The two inductive families the reachability and dilution proof trees induct on.
`Vault.Reachable` (used in `Reachable.lean`) collects the states reachable from a
`Vault.create_lawful` under the vault operations; `Vault.ReachableFromIn` (used in
`Dilution.lean`) additionally tracks the source vault and the operation count, and
restricts to margin-respecting, non-loss-waiving histories. They live here, apart
from the headline files, so the induction proofs can be extracted into `Common`
without an import cycle. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Lawful states reachable from `Vault.create_lawful` under all operations. The ops
return `Vault`, so every reachable state is lawful by construction -/
inductive Vault.Reachable : Vault → Prop where
  | create (nt : NumericType) (scale : UInt8) (assetsMaximum : Option Number)
      (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized)
      (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat)
      (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
      Vault.Reachable (Vault.create_lawful nt scale assetsMaximum hmax_norm hmax_pos hscale_int hscale_le)
  | deposit (v : Vault) (amount : STAmount) (isDonation : Bool) (r : DepositResult) :
      Vault.Reachable v → v.deposit amount isDonation = .ok r →
      amount.Canonical → -- the deposit amount is a stored-canonical user input
      0 ≤ amount.toRat → -- and is not negative
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | withdraw (v : Vault) (amount : WithdrawAmount) (waive : Bool) (r : WithdrawResult) :
      Vault.Reachable v → v.withdraw amount waive = .ok r →
      r.sharesBurned.IntegralCanonical → -- the burned shares are canonical int64
      r.sharesBurned.mNumericType = .int64 →
      r.sharesBurned.negative = false →
      r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) → -- within the share total
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | clawback (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult) :
      Vault.Reachable v → v.clawback assets holderShares = .ok r →
      assets.Canonical → -- the clawback amount is a stored-canonical user input
      holderShares.IntegralCanonical → -- the holder balance is a stored integral MPT amount
      holderShares.Canonical → -- and value-exact through toNumber
      holderShares.negative = false → -- a balance is nonnegative
      r.sharesDestroyed.toRat < (v.toExact.sharesTotal : ℚ) → -- strictly partial
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | burnShares (v : Vault) (sharesDestroyed sharesTotalAmount : STAmount) (v' : Vault) :
      Vault.Reachable v →
      v.canBurnShares = .ok (.assets sharesTotalAmount) → -- the burn permission guard passed
      sharesDestroyed.IntegralCanonical → -- stored as a plain integral amount
      sharesDestroyed.negative = false →
      sharesDestroyed.toRat ≤ sharesTotalAmount.toRat → -- a holder cannot burn more than exists
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      v.burnShares sharesDestroyed = .ok v' →
      Vault.Reachable v'

/-- `Vault.ReachableFromIn w v n` holds when `v` results from `w` by `n`
operations that ran without a throw. Loss-waiving withdrawals are excluded,
matching `withdraw_no_dilution`. -/
inductive Vault.ReachableFromIn : Vault → Vault → ℕ → Prop where
  | refl (w : Vault) : Vault.ReachableFromIn w w 0
  | deposit (w u : Vault) (n : ℕ) (amount : STAmount) (isDonation : Bool)
      (r : DepositResult) :
      Vault.ReachableFromIn w u n → u.deposit amount isDonation = .ok r →
      amount.Canonical → -- the deposit amount is a stored-canonical user input
      0 < amount.toRat → -- the deposited amount is positive, the preflight guard
      r.amountDeposit'.isZero = false → -- the taken amount does not underflow to zero (deposit_no_dilution `hcnz`)
      (u.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 → -- share domain
      Vault.ReachableFromIn w r.vault' (n + 1)
  | withdraw (w u : Vault) (n : ℕ) (amount : WithdrawAmount) (r : WithdrawResult) :
      Vault.ReachableFromIn w u n → u.withdraw amount false = .ok r →
      u.WithdrawNavExact false → -- the two pricing subtractions do not round (withdraw_payout)
      r.assets'.isZero = false → -- the payout does not underflow to zero (withdraw_no_dilution `hcnz`)
      r.sharesBurned.IntegralCanonical → -- the burned shares are canonical int64
      r.sharesBurned.Canonical → -- and value-exact through `toNumber`
      r.sharesBurned.mNumericType = .int64 →
      r.sharesBurned.negative = false →
      -- near-final margin: at least half the shares remain, so the withdraw step respects
      -- `withdraw_no_dilution` (this honestly restricts to margin-respecting histories)
      r.sharesBurned.toRat ≤ (u.toExact.sharesTotal : ℚ) / 2 →
      (u.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.ReachableFromIn w r.vault' (n + 1)
  | clawback (w u : Vault) (n : ℕ) (assets holderShares : STAmount) (r : ClawbackResult) :
      Vault.ReachableFromIn w u n → u.clawback assets holderShares = .ok r →
      u.WithdrawNavExact false → -- the two pricing subtractions do not round (clawback_assetsRecovered)
      assets.Canonical → -- the clawed-back amount is a stored-canonical user input
      holderShares.IntegralCanonical → -- the holder balance is a stored integral MPT amount
      holderShares.Canonical → -- and value-exact through toNumber
      holderShares.negative = false → -- a balance is nonnegative
      -- near-final margin: at least half the shares remain, so the clawback step respects
      -- `clawback_no_dilution` (honestly restricts to margin-respecting histories)
      r.sharesDestroyed.toRat ≤ (u.toExact.sharesTotal : ℚ) / 2 →
      (u.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.ReachableFromIn w r.vault' (n + 1)
  | burnShares (w u : Vault) (n : ℕ) (sharesDestroyed sharesTotalAmount : STAmount)
      (u' : Vault) :
      Vault.ReachableFromIn w u n →
      u.canBurnShares = .ok (.assets sharesTotalAmount) → -- the burn permission guard passed
      sharesDestroyed.IntegralCanonical → -- stored as a plain integral amount
      sharesDestroyed.negative = false →
      sharesDestroyed.toRat ≤ sharesTotalAmount.toRat → -- a holder cannot burn more than exists
      0 ≤ sharesDestroyed.toRat →
      sharesDestroyed.toRat.den = 1 → -- shares are an MPT amount, a whole number
      (u.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      u.burnShares sharesDestroyed = .ok u' →
      Vault.ReachableFromIn w u' (n + 1)

end XRPL.Model.SingleAssetVault
