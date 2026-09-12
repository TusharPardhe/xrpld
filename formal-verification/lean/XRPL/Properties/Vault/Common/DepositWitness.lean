import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.DilutionWitness

/-! # Witnesses for the `Vault.deposit` `*_attained` theorems

Concrete vaults, amounts, and results for the deposit `*_attained` witnesses
`VaultDeposit.lean` delegates to, each closed by `native_decide` over the deposit
pipeline. One lawful IOU vault (`wvF`: 3 assets, 7·10¹⁵ shares, nothing
unrealized) backs the three fractional witnesses; an int64 vault (`wvDVU`) backs
the vault-updates witness.

* Truncation: depositing `0.4444444444444445` (`wtF`) floors on the `10^(-15)`
  grid to `0.444444444444444` (`wtrF`), strictly below the deposit.
* Shares: depositing `1` (`waF`) prices `7·10¹⁵ / 3` shares, truncated to
  `2333333333333333` (`wsF`); the error `1/3` exceeds the relative budget.
* Charge: the share round-trip first returns `0.9999999999999999` (`wcF`), then
  the source-faithful deposit clamp stores `0.9999999999999990` (`wcfF`); the
  resulting charge still exceeds the relative-only budget.
* RawVault updates: donating `9000000000000000006` int64 (`waDVU`) makes the exact
  new total `18000000000000000013`, rounded to `18000000000000000010`, so the
  stored total is not the exact sum.
* Clamp/update pair: depositing `0.001` (`waAD`) produces raw charge
  `0.0009999999999998572` (`wcAD`), clamped to
  `0.0009999999999990000` (`wcrAD`); precisely that final value drives both
  asset-state updates. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Witness data for the fractional sharpness theorems -/

/-- The shared fractional witness vault: 3 assets, 7·10¹⁵ shares. -/
def wvF : RawVault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

/-- The witness deposit amount, `1` of the IOU. -/
def waF : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- The issued shares, `⌊7·10¹⁵/3⌋ = 2333333333333333`. -/
def wsF : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The raw `computeDeposit` amount: `3 · 2333333333333333 / 7·10¹⁵` rounded
upward at 16 digits, `0.9999999999999999`. -/
def wcF : STAmount := STAmount.unchecked .fractional 9999999999999999 (-16) false

/-- The final stored deposit after the posterior-total clamp,
`0.9999999999999990`. -/
def wcfF : STAmount := STAmount.unchecked .fractional 9999999999999990 (-16) false

/-- The post-deposit vault, updated with the final clamped deposit. -/
def wvF' : RawVault :=
  { assetsTotal := ⟨false, 3999999999999999000, -18⟩
  , assetsAvailable := ⟨false, 3999999999999999000, -18⟩
  , assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 9333333333333333000, -3⟩
  , lossUnrealized := Number.zero }

/-- The post-deposit vault as a `Vault` (the op re-validates on success). -/
def wvF'L : Vault := ⟨wvF', by native_decide, by native_decide⟩

/-- The witness deposit result, which records the final clamped amount. -/
def wrF : DepositResult := ⟨none, wvF'L, wcfF, wsF⟩

/-- The truncation witness deposit amount, `0.4444444444444445`. -/
def wtF : STAmount := STAmount.unchecked .fractional 4444444444444445 (-16) false

/-- The truncated deposit amount on the vault grid, `0.444444444444444`. -/
def wtrF : STAmount := STAmount.unchecked .fractional 4444444444444440 (-16) false

/-! ## Witness data for `deposit_vault_updates_attained`

An int64 vault holding `9000000000000000007` with `10¹⁸` shares outstanding. A
donation of the integral amount `9000000000000000006` makes the exact new total
`18000000000000000013`, which is 20 digits and rounds to nearest at 19
significant digits, storing `18000000000000000010`. That stored value differs
from the exact sum, so the `depositε` error term in `deposit_vault_updates`
cannot be dropped. -/

/-- The witness vault. -/
def wvDVU : RawVault :=
  { assetsTotal := ⟨false, 9000000000000000007, 0⟩
  , assetsAvailable := ⟨false, 9000000000000000007, 0⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, 0⟩
  , lossUnrealized := Number.zero }

/-- The witness donation amount, `9000000000000000006` int64. -/
def waDVU : STAmount := STAmount.unchecked .int64 9000000000000000006 0 false

/-- The post-donation vault: both asset fields store `18000000000000000010`, the
exact sum `18000000000000000013` rounded to 19 significant digits. -/
def wvDVU' : RawVault :=
  { assetsTotal := ⟨false, 1800000000000000001, 1⟩
  , assetsAvailable := ⟨false, 1800000000000000001, 1⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, 0⟩
  , lossUnrealized := Number.zero }

/-- The post-donation vault as a `Vault` (the op re-validates on success). -/
def wvDVU'L : Vault := ⟨wvDVU', by native_decide, by native_decide⟩

/-- The witness deposit result. -/
def wrDVU : DepositResult := ⟨none, wvDVU'L, waDVU, STAmount.zero .int64⟩

/-! ## The `*_attained` witnesses -/

set_option maxRecDepth 10000

/-- The fractional witness vault, packaged as a `Vault`. -/
def wvFL : Vault := ⟨wvF, by native_decide, by native_decide⟩

/-- The vault-updates witness vault, packaged as a `Vault`. -/
def wvDVUL : Vault := ⟨wvDVU, by native_decide, by native_decide⟩

/-- Witness backing `Vault.roundedDepositAmount_truncation_attained`. -/
theorem Vault.roundedDepositAmount_truncation_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  ⟨wvFL, wtF, wtrF, by native_decide⟩

/-- Witness backing `Vault.deposit_sharesIssued_attained`. -/
theorem Vault.deposit_sharesIssued_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesIssued
        (v.idealSharesDeposit roundedAmount.toRat) depositε :=
  ⟨wvFL, waF, waF, wrF, by native_decide, by native_decide,
    by native_decide, by native_decide, by unfold RoundsWithinWitness; native_decide⟩

/-- Witness backing `Vault.deposit_charge_attained`. -/
theorem Vault.deposit_charge_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.amountDeposit'
        (v.idealChargeDeposit r.sharesIssued.toRat) depositε :=
  ⟨wvFL, waF, wrF, by native_decide, by native_decide,
    by native_decide, by unfold RoundsWithinWitness; native_decide⟩

/-- Witness backing `Vault.deposit_vault_updates_attained`. -/
theorem Vault.deposit_vault_updates_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (r : DepositResult),
      v.deposit amountDeposit isDonation = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal + r.amountDeposit'.toRat :=
  ⟨wvDVUL, waDVU, true, wrDVU, by native_decide⟩

/-- The applied-delta witness request, `0.001` of the IOU. -/
def waAD : STAmount := STAmount.unchecked .fractional 1000000000000000 (-18) false

/-- The issued shares, `⌊7·10¹⁵ · 0.001 / 3⌋ = 2333333333333`. -/
def wsAD : STAmount := STAmount.unchecked .int64 2333333333333 0 false

/-- The charge: `3 · 2333333333333 / 7·10¹⁵` rounded upward at 16 digits,
`0.0009999999999998572`. -/
def wcAD : STAmount := STAmount.unchecked .fractional 9999999999998572 (-19) false

/-- The charge re-rounded to the vault scale, `0.000999999999999`. -/
def wcrAD : STAmount := STAmount.unchecked .fractional 9999999999990000 (-19) false

/-- The post-deposit vault: both asset totals store `3.000999999999999`,
updated by the final clamped deposit. -/
def wvAD' : RawVault :=
  { assetsTotal := ⟨false, 3000999999999999000, -18⟩
  , assetsAvailable := ⟨false, 3000999999999999000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7002333333333333000, -3⟩
  , lossUnrealized := Number.zero }

/-- The post-deposit vault as a `Vault` (the op re-validates on success). -/
def wvAD'L : Vault := ⟨wvAD', by native_decide, by native_decide⟩

/-- The witness deposit result, which records the final clamped amount. -/
def wrAD : DepositResult := ⟨none, wvAD'L, wcrAD, wsAD⟩

/-- The exact `Number` converted from the final deposit and credited to both
asset fields in the clamp-rounding run. -/
def wdnAD : Number := ⟨false, 9999999999990000000, -22⟩

/-- Witness backing a real raw-to-final clamp rounding in a non-donation
`Vault.deposit`. The raw `computeDeposit` asset differs from the final amount
recorded by the successful operation. -/
theorem Vault.deposit_clamp_rounding_witness :
    ∃ (v : Vault) (amountDeposit rawDeposit : STAmount) (r : DepositResult),
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      (match computeDeposit v amountDeposit with
        | .ok (.success assets _) => assets.operator_eq rawDeposit
        | _ => false) = true ∧
      clampToSumExponent v.assetsTotal rawDeposit = .ok r.amountDeposit' ∧
      rawDeposit.operator_eq r.amountDeposit' = false :=
  ⟨wvFL, waAD, wcAD, wrAD, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Witness that the final clamped deposit, rather than the raw compute-stage
amount, is converted and added to both stored asset fields. -/
theorem Vault.deposit_final_deposit_updates_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
      (assetDeposited : Number),
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.amountDeposit'.toNumber .to_nearest = .ok assetDeposited ∧
      v.assetsTotal.operator_add assetDeposited .to_nearest = .ok r.vault'.assetsTotal ∧
      v.assetsAvailable.operator_add assetDeposited .to_nearest = .ok r.vault'.assetsAvailable :=
  ⟨wvFL, waAD, wrAD, wdnAD, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
