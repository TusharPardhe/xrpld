import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.RoundtripProofs

/-! # Depositing and redeeming returns the taken amount

In exact arithmetic the round trip is the identity: a deposit at the NAV rate
does not change the rate, so the issued shares are worth exactly the taken
amount, and redeeming them immediately pays it back. Everything else is
rounding, and the directed conversions make the error asymmetric: the charge
rounds up and the payout rounds down, so the round trip can never profit
beyond the stage error, and loses at most the rounding budget. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Depositing and immediately redeeming the issued shares preserves the
source-faithful provenance of both clamps. A real deposit stores the posterior
clamp of its raw exchange charge. The withdrawal then either takes the final
whole-vault exit, or stores and returns the posterior clamp of its raw exchange
payout. The raw and final amounts are intentionally distinct witnesses: concrete
executions demonstrate that neither equality is valid in general. -/
theorem Vault.deposit_withdraw_roundtrip (v : Vault) (amountDeposit : STAmount)
    (r₁ : DepositResult) (r₂ : WithdrawResult)
    (hL : v.toExact.lossUnrealized = 0)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hDc : r₁.amountDeposit'.ExactCanonical)
    (hDnn : 0 ≤ r₁.amountDeposit'.toRat)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok₁ : v.deposit amountDeposit false = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂)
    (herr₂ : r₂.error = none) :
    ∃ (rawDeposit : STAmount) (cw : ComputeWithdrawResult) (sharesTotalAmount : STAmount),
      clampToSumExponent v.assetsTotal rawDeposit = .ok r₁.amountDeposit' ∧
      computeWithdrawByShares r₁.vault' r₁.sharesIssued false = .ok cw ∧
      cw.error = none ∧
      STAmount.ofNumber .int64 r₁.vault'.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r₂.sharesBurned = cw.sharesRedeemed ∧
      ((cw.sharesRedeemed.operator_eq sharesTotalAmount = true ∧
        r₁.vault'.lossUnrealized.operator_ne Number.zero = false ∧
        ∃ allAvailable : STAmount,
          STAmount.ofNumber r₁.vault'.numericType r₁.vault'.assetsAvailable .to_nearest = .ok allAvailable ∧
          r₂.assets' = allAvailable) ∨
       (cw.sharesRedeemed.operator_eq sharesTotalAmount = false ∧
        clampToSumExponent r₁.vault'.assetsTotal cw.assets'.operator_neg = .ok r₂.assets' ∧
        r₂.assets'.isFractionalNonPositive = .ok false)) :=
  Vault.deposit_withdraw_roundtrip_proof v amountDeposit r₁ r₂ hL hpos hcanon hAV
    hDc hDnn hSsz hok₁ herr₁ hok₂ herr₂


/-- A concrete round trip with independently observed raw-to-final corrections
on both sides and exact equality of the final credited and paid amounts. -/
theorem Vault.deposit_withdraw_roundtrip_clamp_correction_attained :
    ∃ (v : Vault) (amountDeposit rawDeposit rawPayout : STAmount)
      (r₁ : DepositResult) (r₂ : WithdrawResult),
      0 < amountDeposit.toRat ∧
      v.toExact.lossUnrealized = 0 ∧
      v.deposit amountDeposit false = .ok r₁ ∧ r₁.error = none ∧
      clampToSumExponent v.assetsTotal rawDeposit = .ok r₁.amountDeposit' ∧
      rawDeposit.operator_eq r₁.amountDeposit' = false ∧
      (match computeWithdrawByShares r₁.vault' r₁.sharesIssued false with
        | .ok cw => cw.assets'.operator_eq rawPayout
        | .error _ => false) = true ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂ ∧ r₂.error = none ∧
      clampToSumExponent r₁.vault'.assetsTotal rawPayout.operator_neg = .ok r₂.assets' ∧
      rawPayout.operator_eq r₂.assets' = false ∧
      r₂.assets'.operator_eq r₁.amountDeposit' = true :=
  Vault.deposit_withdraw_roundtrip_clamp_correction_attained_proof

end XRPL.Model.SingleAssetVault
