import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DilutionWitness

/-! # Witness data for the `Vault.withdraw` sharpness theorems

Concrete vaults, amounts, and results for the withdraw `*_attained`
witnesses `VaultWithdraw.lean` delegates to, each closed by `native_decide`
over the withdraw pipeline. One fractional vault holding `3` assets against
`7·10¹⁵` shares backs every witness.

* Witnesses for `sharesToAssetsWithdraw`, `withdraw_sharesBurned` and
  `withdraw_payout`: withdrawing the amount `1` prices
  `7·10¹⁵ / 3 = 2333333333333333.33…` shares, rounded to `2333333333333333`
  whole shares. The share error `1/3` exceeds the relative budget
  `ideal · depositε`. The share-price stage computes
  `3 · 2333333333333333 / 7·10¹⁵ = 0.99999999999999985714…`, converted downward
  at 16 digits to `0.9999999999999998`. The non-final `withdraw` path then
  source-faithfully clamps that raw amount to `0.9999999999999990` before it
  updates either stored asset field. The final shortfall still exceeds
  `ideal · depositε < 10^(-17)`.
* Boundary witness: redeeming `2333333333333` shares computes
  `0.0009999999999998571`, then the same clamp produces
  `0.0009999999999990000`; its stored totals use that final debit. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

set_option linter.style.nativeDecide false

/-- The shared withdraw witness vault: 3 assets, 7·10¹⁵ shares. -/
def wvW : RawVault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

/-- The withdraw witness vault as a `Vault`. -/
def wvWL : Vault := ⟨wvW, by native_decide, by native_decide⟩

/-- The asset-denominated witness amount, `1` of the IOU. -/
def waW : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- The redeemed shares, `7·10¹⁵/3` rounded to nearest: `2333333333333333`. -/
def wshW : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The raw share-price result: `3 · 2333333333333333 / 7·10¹⁵` rounded
 downward at 16 digits, `0.9999999999999998`. -/
def wpRawW : STAmount := STAmount.unchecked .fractional 9999999999999998 (-16) false

/-- The final payout after the non-final withdrawal clamp,
`0.9999999999999990`. -/
def wpW : STAmount := STAmount.unchecked .fractional 9999999999999990 (-16) false

/-- The stored share total as an int64 amount, `7000000000000000`. -/
def wstW : STAmount := STAmount.unchecked .int64 7000000000000000 0 false

/-- The post-withdrawal vault of the asset-denominated run. -/
def wvW' : RawVault :=
  { assetsTotal := ⟨false, 2000000000000001000, -18⟩
  , assetsAvailable := ⟨false, 2000000000000001000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 4666666666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The post-withdrawal vault as a `Vault` (the op re-validates). -/
def wvW'L : Vault := ⟨wvW', by native_decide, by native_decide⟩

/-- The witness result of the asset-denominated run. -/
def wrW : WithdrawResult := ⟨none, wvW'L, wpW, wshW⟩

/-- The share-denominated witness shares of the vault-updates run,
`2333333333333`. -/
def wsh4W : STAmount := STAmount.unchecked .int64 2333333333333 0 false

/-- The raw share-price result of the boundary run:
`0.0009999999999998571`. -/
def wpRaw4W : STAmount := STAmount.unchecked .fractional 9999999999998571 (-19) false

/-- The final payout of the boundary run after the non-final withdrawal clamp,
`0.0009999999999990000`. -/
def wp4W : STAmount := STAmount.unchecked .fractional 9999999999990000 (-19) false

/-- The post-withdrawal vault of the boundary run, updated by subtracting the
final clamped payout from both asset fields. -/
def wv4W' : RawVault :=
  { assetsTotal := ⟨false, 2999000000000001000, -18⟩
  , assetsAvailable := ⟨false, 2999000000000001000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 6997666666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The vault-updates post-withdrawal vault as a `Vault` (the op re-validates). -/
def wv4W'L : Vault := ⟨wv4W', by native_decide, by native_decide⟩

/-- The witness result of the vault-updates run. -/
def wr4W : WithdrawResult := ⟨none, wv4W'L, wp4W, wsh4W⟩

/-! ## The `*_attained` witnesses -/

set_option maxRecDepth 10000

/-- Witness data for `Vault.sharesToAssetsWithdraw_attained`. -/
theorem Vault.sharesToAssetsWithdraw_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      RoundsWithinWitness assets
        (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) depositε := by
  refine ⟨wvWL, wshW, wpRawW, false, by native_decide, ?_,
    by native_decide, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness data for `Vault.withdraw_sharesBurned_attained`. -/
theorem Vault.withdraw_sharesBurned_witness :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      0 < assets.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesBurned
        (v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat) depositε := by
  refine ⟨wvWL, waW, false, wrW, by native_decide, ?_,
    by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness data for `Vault.withdraw_payout_attained`. -/
theorem Vault.withdraw_payout_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      RoundsWithinWitness r.assets'
        (v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat) depositε := by
  refine ⟨wvWL, .vaultAssets waW, false, wstW, wrW, ?_,
    by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness data for a real raw-to-final clamp rounding in non-final withdrawal.
The raw share-price result and final payout are distinct, and the latter is
exactly the result of the source-faithful clamp. -/
theorem Vault.withdraw_clamp_rounding_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (rawPayout : STAmount) (r : WithdrawResult),
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      (match amount with
        | .vaultAssets assets => do return (← computeWithdrawByAssets v assets waiveUnrealizedLoss).assets'
        | .vaultShares shares => do return (← computeWithdrawByShares v shares waiveUnrealizedLoss).assets') = .ok rawPayout ∧
      clampToSumExponent v.assetsTotal rawPayout.operator_neg = .ok r.assets' ∧
      rawPayout.operator_eq r.assets' = false := by
  refine ⟨wvWL, .vaultAssets waW, false, wpRawW, wrW, ?_, ?_, ?_, ?_, ?_⟩ <;>
    native_decide

/-- The exact `Number` converted from the final payout and debited from both
asset fields of the asset-denominated run. -/
def wdnW : Number := ⟨false, 9999999999999990000, -19⟩

/-- Witness data that the final payout, not the raw pre-clamp amount, is the
exact `Number` used by both non-final asset-state subtractions. -/
theorem Vault.withdraw_final_debit_updates_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult) (assetDebited : Number),
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      r.assets'.toNumber .to_nearest = .ok assetDebited ∧
      v.assetsTotal.operator_sub assetDebited .to_nearest = .ok r.vault'.assetsTotal ∧
      v.assetsAvailable.operator_sub assetDebited .to_nearest = .ok r.vault'.assetsAvailable := by
  refine ⟨wvWL, .vaultAssets waW, false, wstW, wrW, wdnW, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    native_decide

end XRPL.Model.SingleAssetVault
