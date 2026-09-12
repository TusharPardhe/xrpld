import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.ClawbackReduction
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Vault.Common.ClawbackWitness

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (rv : RawVault) (v : Vault)

theorem RawVault.idealAssetsClawback_idealSharesClawback (assets : ℚ)
    (hnav : rv.withdrawNav ≠ 0) (hsh : rv.toExact.sharesTotal ≠ 0) :
    rv.idealAssetsClawback (rv.idealSharesClawback assets) = assets :=
  RawVault.idealAssetsClawback_idealSharesClawback_proof rv assets hnav hsh

/-- Post-fix clawback uses truncated shares, not nearest share rounding. -/
theorem Vault.clawback_sharesDestroyed (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assets.toRat * (1 - depositε) - 1 < r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤ v.idealSharesClawback assets.toRat * (1 + depositε) :=
  Vault.clawback_sharesDestroyed_proof v assets holderShares sharesDestroyed assetsRecovered
    assetsRecoveredNumber r hnav hc hshares hassets hnum hle hznz hok herr

theorem Vault.clawback_sharesDestroyed_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed (v.idealSharesClawback assets.toRat) depositε :=
  Vault.clawback_sharesDestroyed_witness

theorem Vault.clawback_sharesDestroyed_clamped (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered')
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assetsRecovered'.toRat * (1 - depositε) - 1 < r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤ v.idealSharesClawback assetsRecovered'.toRat * (1 + depositε) :=
  Vault.clawback_sharesDestroyed_clamped_proof v assets holderShares sharesDestroyed assetsRecovered
    assetsRecovered' assetsRecoveredNumber r hnav hshares hassets hnum hgt hclamped hznz hok herr

theorem Vault.clawback_sharesDestroyed_clamped_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed (v.idealSharesClawback assetsRecovered'.toRat) depositε :=
  Vault.clawback_sharesDestroyed_clamped_witness

/-- Zero clawback preserves the holder share amount but returns the accepted
posterior-clamped recovery, never the raw conversion by assertion. -/
theorem Vault.clawback_zero_all_shares
    (assets holderShares rawAssetsRecovered finalAssetsRecovered : STAmount)
    (rawAssetsRecoveredNumber : Number) (r : ClawbackResult)
    (hz : assets.isZero = true)
    (hassets : v.sharesToAssetsWithdraw holderShares false = .ok rawAssetsRecovered)
    (hnum : rawAssetsRecovered.toNumber .to_nearest = .ok rawAssetsRecoveredNumber)
    (hle : rawAssetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hclamp : clampToSumExponent v.assetsTotal rawAssetsRecovered.operator_neg = .ok finalAssetsRecovered)
    (hprecision : finalAssetsRecovered.isFractionalNonPositive = .ok false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed = holderShares ∧ r.assetsRecovered = finalAssetsRecovered ∧ holderShares.isZero = false :=
  Vault.clawback_zero_all_shares_proof v assets holderShares rawAssetsRecovered finalAssetsRecovered
    rawAssetsRecoveredNumber r hz hassets hnum hle hclamp hprecision hok herr

/-- Raw recovery, posterior clamp, precision guard, and final returned recovery
are explicitly separate facts of a successful clawback. -/
theorem Vault.clawback_assetsRecovered (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ (sharesDestroyed rawRecovered finalRecovered : STAmount),
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawRecovered ∧
      clampToSumExponent v.assetsTotal rawRecovered.operator_neg = .ok finalRecovered ∧
      finalRecovered.isFractionalNonPositive = .ok false ∧
      r.sharesDestroyed = sharesDestroyed ∧ r.assetsRecovered = finalRecovered :=
  Vault.clawback_assetsRecovered_proof v assets holderShares r hnav hc hznz hok herr

theorem Vault.clawback_assetsRecovered_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.assetsRecovered
        (v.idealAssetsClawback r.sharesDestroyed.toRat) depositε :=
  Vault.clawback_assetsRecovered_witness

theorem Vault.clawback_assetsRecovered_integral (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnav : v.WithdrawNavExact false) (hint : v.numericType.isIntegral = true)
    (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ (sharesDestroyed rawRecovered finalRecovered : STAmount),
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawRecovered ∧
      clampToSumExponent v.assetsTotal rawRecovered.operator_neg = .ok finalRecovered ∧
      finalRecovered.isFractionalNonPositive = .ok false ∧
      r.sharesDestroyed = sharesDestroyed ∧ r.assetsRecovered = finalRecovered :=
  Vault.clawback_assetsRecovered_integral_proof v assets holderShares r hnav hint hc hznz hok herr

/-- Stored rails use the final recovered Number and are exposed exactly by the
modeled successful state record. -/
theorem Vault.clawback_vault_updates (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ClawbackFinalState v assets holderShares r :=
  Vault.clawback_vault_updates_proof v assets holderShares r hnav hc hznz hok herr

theorem Vault.clawback_vault_updates_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
      r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat :=
  Vault.clawback_vault_updates_witness

theorem Vault.clawback_applied_delta_attained :
    ∃ (v : Vault) (assets holderShares clamped sharesDestroyed rawRecovered finalRecovered : STAmount)
      (r : ClawbackResult),
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok clamped ∧
      assetsToSharesWithdraw v clamped true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawRecovered ∧
      clampToSumExponent v.assetsTotal rawRecovered.operator_neg = .ok finalRecovered ∧
      finalRecovered.isFractionalNonPositive = .ok false ∧
      finalRecovered.operator_eq rawRecovered = false ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.assetsRecovered = finalRecovered ∧
      r.vault'.assetsTotal = ⟨false, 2999900000000001000, -18⟩ ∧
      r.vault'.assetsAvailable = ⟨false, 1000000000000000000, -33⟩ :=
  Vault.clawback_applied_delta_witness

theorem Vault.clawback_vault_updates_integral (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hint : v.numericType.isIntegral = true) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assetsRecovered.toRat) (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    ClawbackFinalState v assets holderShares r :=
  Vault.clawback_vault_updates_integral_proof v assets holderShares r hint hznz hok herr hnn hsz

end XRPL.Model.SingleAssetVault
