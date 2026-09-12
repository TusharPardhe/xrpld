import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DilutionWitness
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultDeposit

/-! # Witness data for the clawback `*_attained` theorems

Concrete vaults, amounts, and results for the clawback `*_attained`
witnesses `VaultClawback.lean` delegates to, each closed by `native_decide`
over the clawback pipeline. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## The witness vaults, amounts, and results -/

/-- The shared witness vault: 3 assets, 3 available, 7·10¹⁵ shares. -/
def cwv : RawVault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

/-- The clamped-run vault: the same vault with only `0.0001` available. -/
def cwvB : RawVault :=
  { cwv with assetsAvailable := ⟨false, 1000000000000000000, -22⟩ }

/-- Lawful-vault witnesses. -/
def cwvL : Vault := ⟨cwv, by native_decide, by native_decide⟩
def cwvBL : Vault := ⟨cwvB, by native_decide, by native_decide⟩

/-- The clawed amount, `1` of the IOU. -/
def cwa1 : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- Witness holder-shares balance passed to `Vault.clawback`. Unused on these
runs since `cwa1` is nonzero (the zero-amount "claw all" branch never fires). -/
def cwHolderShares : STAmount := STAmount.zero .int64

/-- The destroyed shares of the `cwv` run, `2333333333333333`. -/
def cwsh1 : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The raw recovery of the `cwv` share round-trip, `0.9999999999999998`. -/
def cwar1 : STAmount := STAmount.unchecked .fractional 9999999999999998 (-16) false

/-- The direct run's final recovery after the posterior clamp, `0.9999999999999990`. -/
def cwfinal1 : STAmount := STAmount.unchecked .fractional 9999999999999990 (-16) false

/-- The clamped recovery amount of the `cwvB` run, `0.0001`. -/
def cwclamp : STAmount := STAmount.unchecked .fractional 1000000000000000 (-19) false

/-- The destroyed shares of the `cwvB` run, `233333333333`. -/
def cwsh2 : STAmount := STAmount.unchecked .int64 233333333333 0 false

/-- The capped path's raw recovery before its posterior clamp, `0.00009999999999985714`. -/
def cwar2 : STAmount := STAmount.unchecked .fractional 9999999999985714 (-20) false

/-- The capped path's final recovery after the posterior clamp, `0.000099999999999`. -/
def cwfinal2 : STAmount := STAmount.unchecked .fractional 9999999999900000 (-20) false

/-- The `cwv` post-clawback vault. -/
def cwv1' : RawVault :=
  { assetsTotal := ⟨false, 2000000000000001000, -18⟩
  , assetsAvailable := ⟨false, 2000000000000001000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 4666666666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The `cwv` post-clawback vault as a `Vault` (the op re-validates). -/
def cwv1'L : Vault := ⟨cwv1', by native_decide, by native_decide⟩

/-- The `cwv` clawback result returns the final, clamped recovery. -/
def cwr1 : ClawbackResult := ⟨none, cwv1'L, cwfinal1, cwsh1⟩

/-- The `cwvB` post-clawback vault. -/
def cwvB' : RawVault :=
  { assetsTotal := ⟨false, 2999900000000001000, -18⟩
  , assetsAvailable := ⟨false, 1000000000000000000, -33⟩
  , assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 6999766666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The `cwvB` post-clawback vault as a `Vault` (the op re-validates). -/
def cwvB'L : Vault := ⟨cwvB', by native_decide, by native_decide⟩

/-- The `cwvB` clawback result returns the final, clamped recovery. -/
def cwr2 : ClawbackResult := ⟨none, cwvB'L, cwfinal2, cwsh2⟩

/-! ## The `*_attained` witnesses -/

set_option maxRecDepth 10000

/-- Witness for `Vault.clawback_sharesDestroyed_attained`: the `cwv` run's
half-share rounding error `1/3` exceeds the relative budget alone. -/
theorem Vault.clawback_sharesDestroyed_witness :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧
      assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (v.idealSharesClawback assets.toRat) depositε := by
  refine ⟨cwvL, cwa1, cwHolderShares, cwsh1, cwar1, ⟨false, 9999999999999998000, -19⟩, cwr1,
    ?_, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness for `Vault.clawback_sharesDestroyed_clamped_attained`: the `cwvB`
run reprices from `assetsAvailable` and its truncation error `1/3` exceeds the
relative budget alone. -/
theorem Vault.clawback_sharesDestroyed_clamped_witness :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧
      assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (v.idealSharesClawback assetsRecovered'.toRat) depositε := by
  refine ⟨cwvBL, cwa1, cwHolderShares, cwsh1, cwar1, cwclamp, ⟨false, 9999999999999998000, -19⟩, cwr2,
    ?_, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness for `Vault.clawback_assetsRecovered_attained`: the `cwv` run's
recovery misses the destroyed shares' exact worth by more than the relative
budget. -/
theorem Vault.clawback_assetsRecovered_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ v.clawback assets holderShares = .ok r ∧
      r.error = none ∧
      RoundsWithinWitness r.assetsRecovered
        (v.idealAssetsClawback r.sharesDestroyed.toRat) depositε := by
  refine ⟨cwvL, cwa1, cwHolderShares, cwr1,
    ?_, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness for `Vault.clawback_vault_updates_attained`: the capped run stores
exact final-recovery deltas on both asset rails after the posterior clamp. -/
theorem Vault.clawback_vault_updates_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
      r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat :=
  ⟨cwvBL, cwa1, cwHolderShares, cwr2, by native_decide⟩

/-- Witness for `Vault.clawback_applied_delta_attained`: after the available-cap
reprice, the raw recovery is distinct from the posterior-clamped final recovery;
the committed result and all stored rails use that final recovery. -/
theorem Vault.clawback_applied_delta_witness :
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
  ⟨cwvBL, cwa1, cwHolderShares, cwclamp, cwsh2, cwar2, cwfinal2, cwr2, by native_decide⟩

/-! ## Clawback-all empty-shares dust witness -/

/-- Dust witness vault: π assets/available (16-digit IOU), 7000025 shares. -/
def clawbackDustVault : RawVault :=
  { assetsTotal := ⟨false, 3141592653589793000, -18⟩
  , assetsAvailable := ⟨false, 3141592653589793000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000025000000000000, -12⟩
  , lossUnrealized := Number.zero }

/-- The dust witness vault as a `Vault`. -/
def clawbackDustVaultL : Vault := ⟨clawbackDustVault, by decide, by decide⟩

/-- Witness that `clawback_success`'s `hempty` is meaningful: clawing back all
shares of a lawful vault can leave sub-ULP `assetsTotal` dust (`sharesTotal' = 0`,
`assetsTotal' ≠ 0`), so `to_lawful` rejects with `notLawful`. -/
theorem Vault.clawback_dust_witness :
    clawbackDustVaultL.clawback (STAmount.zero .fractional)
        (STAmount.unchecked .int64 7000025 0 false) = .error .notLawful := by
  native_decide

end XRPL.Model.SingleAssetVault
