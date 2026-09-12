import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Witness data for the `*_dilution_attained` sharpness theorems

Concrete lawful vault states and operations that strictly decrease per-share
value, backing the `*_dilution_attained` headlines in `Dilution.lean`. The
starting state `baseV` is the IOU state reached through the public API (scale
`6`, seed deposit `899999999.876543`, donation `123.4567891`). The withdrawal
and clawback vector is derived from its exact ratio: with
`n = 90988822812816`, writing `A = 9000001233333321` and
`S = 899999999876543`, `A * n % S = S - 1`. Thus the ideal payout is one
rational unit below a `10⁻⁷` vault-scale grid point; the source-faithful
nearest-number exchange followed by the downward posterior-scale clamp returns
that grid point, strictly decreasing the remaining holders' value. The concrete
runs and strict inequalities are closed by `native_decide` only after this
independent derivation.

`native_decide` compiles the decidable propositions to native code and trusts the
result through the `Lean.ofReduceBool` axiom. It is confined to these concrete
sharpness witnesses; kernel-checked universal proofs (the `*_no_dilution`
bounds) never use it.

The `Decidable` instances for the vault predicates (`RawVault.WF`, `RawVault.Valid`,
`RawVault.Exact.Valid`, and the `STAmount` canonical shapes) let `native_decide` close
the concrete checks; every clause is a decidable arithmetic or storage-shape
condition, and the `assetsMaximum` quantifier ranges over an `Option` (here always
`none`). -/

-- `native_decide` is the approved mechanism for these sharpness witnesses (it trusts the
-- compiler through `Lean.ofReduceBool`); the universal `*_no_dilution` bounds never use it.
set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Decidable instances for the concrete none-cap witness states -/

instance STAmount.instDecidableIntegralCanonical (s : STAmount) : Decidable s.IntegralCanonical :=
  decidable_of_iff
    (s.mNumericType.isIntegral = true ∧ s.mOffset = 0 ∧
      s.mValue.toNat ≤ s.mNumericType.maxValue.toNat)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

instance STAmount.instDecidableIOUCanonical (s : STAmount) : Decidable s.IOUCanonical :=
  decidable_of_iff
    (s.mNumericType = .fractional ∧ 10 ^ 15 ≤ s.mValue.toNat ∧ s.mValue.toNat < 10 ^ 16 ∧
      (-96 : ℤ) ≤ s.mOffset ∧ s.mOffset ≤ 80)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

instance STAmount.instDecidableCanonical (s : STAmount) : Decidable s.Canonical := by
  unfold STAmount.Canonical; infer_instance

instance STAmount.instDecidableExactCanonical (s : STAmount) : Decidable s.ExactCanonical := by
  unfold STAmount.ExactCanonical; infer_instance

instance RawVault.Exact.instDecidableValid (s : RawVault.Exact) : Decidable s.Valid :=
  decidable_of_iff
    (0 ≤ s.assetsTotal ∧ 0 ≤ s.assetsAvailable ∧ s.assetsAvailable ≤ s.assetsTotal ∧
     (∀ m ∈ s.assetsMaximum, 0 < m) ∧
     (s.sharesTotal = 0 → s.assetsTotal = 0 ∧ s.assetsAvailable = 0) ∧
     (∀ m ∈ s.assetsMaximum, s.assetsTotal ≤ m) ∧
     0 ≤ s.lossUnrealized ∧ s.lossUnrealized ≤ s.assetsTotal - s.assetsAvailable ∧
     0 ≤ s.assetsTotal - s.lossUnrealized)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-! ## The base witness vault, amounts, and results -/

/-- The lawful IOU vault the search reaches through the public API:
`assetsTotal = assetsAvailable = 900000123.3333321`, `sharesTotal = 899999999876543`,
nothing unrealized or reserved, no cap, scale `6`. -/
def baseV : RawVault :=
  { assetsTotal := ⟨false, 9000001233333321000, -10⟩
  , assetsAvailable := ⟨false, 9000001233333321000, -10⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 6
  , sharesTotal := ⟨false, 8999999998765430000, -4⟩
  , lossUnrealized := Number.zero }

/-- Witness deposit amount `1587.0335`: the stored-total update rounds against the
vault by more than the charge's upward surplus. -/
def depAmt : STAmount := STAmount.unchecked .fractional 1587033500000000 (-12) false

/-- The grid-point clawback amount `90988835.2941359`. Its exact share value is
one rational unit below this `10⁻⁷` point, while the source-faithful fixed-asset
conversion truncates to `shAmt`. -/
def clawAmt : STAmount := STAmount.unchecked .fractional 9098883529413590 (-8) false

/-- Witness holder-shares balance passed to `Vault.clawback`. Unused on this
run since `clawAmt` is nonzero (the zero-amount "claw all" branch never fires). -/
def clawHolderShares : STAmount := STAmount.zero .int64

/-- Fixed-share boundary witness `n = 90988822812816`. For the base ratio,
`9000001233333321 * n % 899999999876543 = 899999999876542`; hence the exact
payout is one rational unit below its next `10⁻⁷` grid point. -/
def shAmt : STAmount := STAmount.unchecked .int64 90988822812816 0 false

/-- The base witness vault as a `Vault`.

`native_decide` (`Lean.ofReduceBool`) closes the operator forms `WF` and `Valid`,
both Model-side computable; `Vault.exact` (via `valid_iff_exact`) then supplies
the exact-rational invariant wherever a proof consumes it. -/
def baseLV : Vault := ⟨baseV, by native_decide, by native_decide⟩

/-- The deposit result. `getD` never fires (the run succeeds); the fallback keeps
the definition total. -/
def depR : DepositResult :=
  (baseLV.deposit depAmt false).toOption.getD (DepositResult.rejected baseLV .tecINTERNAL)

/-- The withdrawal result. -/
def wdR : WithdrawResult :=
  (baseLV.withdraw (.vaultShares shAmt) false).toOption.getD (WithdrawResult.rejected baseLV .tecINTERNAL)

/-- The clawback result. -/
def clawR : ClawbackResult :=
  (baseLV.clawback clawAmt clawHolderShares).toOption.getD (ClawbackResult.rejected baseLV .tecINTERNAL)

/-- Zero clawed amount for the claw all dilution run. -/
def clawA0 : STAmount := STAmount.zero .fractional

/-- Holder balance of the zero amount run. It is `shAmt` on the successful
nonzero clawback, so the zero-amount all-shares branch has the same boundary
rounding vector. -/
def clawZeroShares : STAmount := clawR.sharesDestroyed

/-- The zero amount clawback result. -/
def clawR0 : ClawbackResult :=
  (baseLV.clawback clawA0 clawZeroShares).toOption.getD (ClawbackResult.rejected baseLV .tecINTERNAL)

/-- Second deposit in the compounding history: the first deposit takes `baseV` to
`depR.vault'`, this one takes it one step further. -/
def r2 : DepositResult :=
  (depR.vault'.deposit depAmt false).toOption.getD (DepositResult.rejected baseLV .tecINTERNAL)

/-! ## The diluting operations, established by native evaluation

Each lemma bundles one operation's success, its `error = none` exit, and the
strict per-share decrease against `baseV` in cross-multiplied form. -/

/-- The deposit succeeds and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem depR_dilutes :
    0 < depAmt.toRat ∧ baseLV.deposit depAmt false = .ok depR ∧ depR.error = none ∧
    depR.vault'.withdrawNav * (baseV.toExact.sharesTotal : ℚ) <
      baseV.withdrawNav * (depR.vault'.toExact.sharesTotal : ℚ) := by native_decide

/-- The withdrawal succeeds and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem wdR_dilutes :
    baseLV.withdraw (.vaultShares shAmt) false = .ok wdR ∧ wdR.error = none ∧
    wdR.vault'.withdrawNav * (baseV.toExact.sharesTotal : ℚ) <
      baseV.withdrawNav * (wdR.vault'.toExact.sharesTotal : ℚ) := by native_decide

/-- The clawback succeeds and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem clawR_dilutes :
    baseLV.clawback clawAmt clawHolderShares = .ok clawR ∧ clawR.error = none ∧
    clawR.vault'.withdrawNav * (baseV.toExact.sharesTotal : ℚ) <
      baseV.withdrawNav * (clawR.vault'.toExact.sharesTotal : ℚ) := by native_decide

/-- The zero-amount clawback destroys exactly the holder's balance (a canonical
nonnegative integral amount) and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem clawR0_dilutes :
    clawA0.isZero = true ∧
    clawZeroShares.IntegralCanonical ∧ clawZeroShares.Canonical ∧
    clawZeroShares.negative = false ∧
    baseLV.clawback clawA0 clawZeroShares = .ok clawR0 ∧ clawR0.error = none ∧
    clawR0.sharesDestroyed = clawZeroShares ∧
    clawR0.vault'.withdrawNav * (baseV.toExact.sharesTotal : ℚ) <
      baseV.withdrawNav * (clawR0.vault'.toExact.sharesTotal : ℚ) := by native_decide

/-- The two-deposit history: each step satisfies its `ReachableFromIn.deposit`
side conditions (canonical storage, positive amount and shares, share domain), and
the endpoint `r2.vault'` strictly dilutes against `baseV`. Bundled so the
`ReachableFromIn` assembly in `Dilution.lean` reuses one native run.

`native_decide` (`Lean.ofReduceBool`). -/
theorem reachable_chain_facts :
    (baseLV.deposit depAmt false = .ok depR ∧ depAmt.Canonical ∧ 0 < depAmt.toRat ∧
      depR.amountDeposit'.ExactCanonical ∧ 0 ≤ depR.amountDeposit'.toRat ∧
      depR.sharesIssued.IntegralCanonical ∧ 0 ≤ depR.sharesIssued.toRat ∧
      (baseV.toExact.sharesTotal : ℚ) + depR.sharesIssued.toRat ≤ 2 ^ 63 - 1) ∧
    (depR.vault'.deposit depAmt false = .ok r2 ∧ depAmt.Canonical ∧ 0 < depAmt.toRat ∧
      r2.amountDeposit'.ExactCanonical ∧ 0 ≤ r2.amountDeposit'.toRat ∧
      r2.sharesIssued.IntegralCanonical ∧ 0 ≤ r2.sharesIssued.toRat ∧
      (depR.vault'.toExact.sharesTotal : ℚ) + r2.sharesIssued.toRat ≤ 2 ^ 63 - 1) ∧
    (r2.vault'.withdrawNav * (baseV.toExact.sharesTotal : ℚ) <
      baseV.withdrawNav * (r2.vault'.toExact.sharesTotal : ℚ)) := by native_decide

/-! ## The `*_witness` existentials the headlines delegate to -/

theorem deposit_dilution_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨baseLV, depAmt, depR, depR_dilutes.1, depR_dilutes.2.1, depR_dilutes.2.2.1,
    depR_dilutes.2.2.2⟩

theorem withdraw_dilution_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult),
      v.withdraw amount false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨baseLV, .vaultShares shAmt, wdR, wdR_dilutes.1, wdR_dilutes.2.1, wdR_dilutes.2.2⟩

theorem clawback_dilution_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨baseLV, clawAmt, clawHolderShares, clawR, clawR_dilutes.1, clawR_dilutes.2.1,
    clawR_dilutes.2.2⟩

theorem clawback_zero_dilution_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      assets.isZero = true ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧
      holderShares.negative = false ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.sharesDestroyed = holderShares ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨baseLV, clawA0, clawZeroShares, clawR0, clawR0_dilutes⟩

/-- Witness backing `ReachableFromIn.dilution_attained`: the two-deposit history
from `baseV` whose endpoint `r2.vault'` strictly dilutes against `baseV`. Each
`.deposit` step's `hcnz` sub-witness is a `by native_decide` (`Lean.ofReduceBool`)
on the concrete run. -/
theorem dilution_attained_witness :
    ∃ (lw u : Vault) (n : ℕ),
      1 < n ∧ Vault.ReachableFromIn lw u n ∧
      u.withdrawNav * (lw.toExact.sharesTotal : ℚ) <
        lw.withdrawNav * (u.toExact.sharesTotal : ℚ) := by
  obtain ⟨⟨h1run, h1can, h1pos, -, -, -, -, h1sz⟩,
         ⟨h2run, h2can, h2pos, -, -, -, -, h2sz⟩, hdil⟩ := reachable_chain_facts
  refine ⟨baseLV, r2.vault', 2, by norm_num, ?_, hdil⟩
  have s0 : Vault.ReachableFromIn baseLV baseLV 0 := .refl baseLV
  have s1 : Vault.ReachableFromIn baseLV depR.vault' 1 :=
    .deposit baseLV baseLV 0 depAmt false depR s0 h1run h1can h1pos (by native_decide) h1sz
  exact .deposit baseLV depR.vault' 1 depAmt false r2 s1 h2run h2can h2pos (by native_decide) h2sz

end XRPL.Model.SingleAssetVault
