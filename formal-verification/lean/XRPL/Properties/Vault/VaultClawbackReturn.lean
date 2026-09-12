import XRPL.Properties.Vault.Common.ClawbackExits
import XRPL.Properties.Vault.Common.Preservation

/-! # `Vault.clawback` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.clawback` -/

/-- A negative `assets` amount: `some .tecINTERNAL`, the vault is unchanged
and nothing is recovered. -/
theorem Vault.clawback_negative_amount (assets holderShares : STAmount)
    (hneg : assets.negative = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecINTERNAL) :=
  Vault.clawback_negative_amount_proof v assets holderShares hneg

/-- The exchange computation destroys zero shares: `some .tecPRECISION_LOSS`
and the vault is unchanged. -/
theorem Vault.clawback_zero_shares (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.clawback_zero_shares_proof v assets holderShares result hcomp herr hz

/-- A nonzero recovery whose subtraction does not change `assetsTotal` rounded
into the vault's `numericType`: `some .tecPRECISION_LOSS`. The guard is marked
"(waiting the C++ fix)" in the model. -/
theorem Vault.clawback_recovery_too_small (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.clawback_recovery_too_small_proof v assets holderShares result sharesDestroyedNumber
    assetsRecoveredNumber at' assetsTotalRounded assetsTotalRounded'
    hcomp herr hz hsN haN hat hrt hrt' hguard

/-- Every guard passes on a clawback: the stored total and available assets each
drop by the recovery and the share total by the destroyed shares, the post-state
is still a `Vault`. -/
theorem Vault.clawback_success (assets holderShares : STAmount) (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber st' av' at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hr_norm : assetsRecoveredNumber.isNormalized) (hr_nn : 0 ≤ assetsRecoveredNumber.toRat)
    (hr_le : assetsRecoveredNumber.toRat ≤ v.assetsTotal.toRat)
    (hd_norm : sharesDestroyedNumber.isNormalized) (hd_nn : 0 ≤ sharesDestroyedNumber.toRat)
    (hd_den : sharesDestroyedNumber.toRat.den = 1)
    (hd_le : sharesDestroyedNumber.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = false)
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st')
    (hav : v.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok av')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ v' : Vault,
      v.clawback assets holderShares =
        .ok ⟨none, v', result.assetsRecovered, result.sharesDestroyed⟩ ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } := by
  obtain ⟨v', htl, hlv'eq⟩ := Vault.clawback_poststate_lawful v assetsRecoveredNumber
    sharesDestroyedNumber at' av' st' hL hAV hr_norm hr_nn hr_le hd_norm hd_nn hd_den hd_le hfit
    hat hav hst hempty
  refine ⟨v', ?_, hlv'eq⟩
  unfold Vault.clawback
  simp only []
  rw [hcomp, ok_bind]
  rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [if_neg (by rw [hz]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [hsN, ok_bind, haN, ok_bind, hat, ok_bind, hrt, ok_bind, hrt', ok_bind]
  rw [if_neg (by rw [hguard]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [hst, ok_bind, hav, ok_bind, htl, ok_bind]
  rfl

/-- Every outcome of a clawback that runs without a throw.

`tecINTERNAL` has two origins: a negative `assets` amount, and the check after
the recomputation against `assetsAvailable` (when the first computed recovery
exceeded `assetsAvailable`, the amount is recomputed from truncated shares,
and a recovery that still exceeds `assetsAvailable` returns `tecINTERNAL`).
xrpld excludes that second check from coverage as believed unreachable, but no
proof exists either way. -/
theorem Vault.clawback_error_codes (assets holderShares : STAmount) (r : ClawbackResult)
    (hok : v.clawback assets holderShares = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecPRECISION_LOSS :=
  Vault.clawback_error_codes_proof v assets holderShares r hok

end XRPL.Model.SingleAssetVault
