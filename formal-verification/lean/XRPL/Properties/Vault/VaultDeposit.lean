import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.Common.DepositChargeFrac
import XRPL.Properties.Vault.Common.DepositWitness
import XRPL.Properties.Vault.Common.DepositMono

/-! # `Vault.deposit` accuracy -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `RawVault.roundedDepositAmount` -/

/-- `roundedAmount` is `amountDeposit` with every digit below some grid step
`10 ^ s` discarded and the digits above kept unchanged, and it is nonzero. As an
equation: `roundedAmount.toRat = ⌊amountDeposit.toRat / 10 ^ s⌋ * 10 ^ s`. The
grid step never exceeds the rounded amount itself (`10 ^ s ≤ |roundedAmount|`),
so the truncation always keeps the leading digit. A fractional `amountDeposit`
need only be canonical: no lower bound on its exponent is required, because the
result being nonzero (`.rounded`, so past the `tecPRECISION_LOSS` guard) already
forces the grid point to survive the 16-digit clamp. -/
theorem Vault.roundedDepositAmount_bounds (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
      (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
    roundedAmount.isZero = false :=
  Vault.roundedDepositAmount_bounds_proof v amountDeposit roundedAmount hcanon hrounded

/-- Witness: the truncation in `roundedDepositAmount_bounds` is not vacuous, a
lawful vault and an `amountDeposit` exist where digits are actually dropped. -/
theorem Vault.roundedDepositAmount_truncation_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  Vault.roundedDepositAmount_truncation_witness

/-- An integral `amountDeposit` passes through `roundedDepositAmount`
unchanged. -/
theorem Vault.roundedDepositAmount_integral (amountDeposit : STAmount)
    (hint : amountDeposit.integral = true) -- an integral vault's amounts are integral
    (hnz : amountDeposit.isZero = false) :
    v.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) :=
  Vault.roundedDepositAmount_integral_proof v amountDeposit hint hnz

/-! ## `Vault.deposit` -/

/-- A successful donation takes exactly `roundedAmount` and issues no shares. -/
theorem Vault.deposit_donation (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.amountDeposit' = roundedAmount ∧ r.sharesIssued = STAmount.zero .int64 :=
  Vault.deposit_donation_proof v amountDeposit roundedAmount r hrounded hok herr


/-- When the vault's exchange rate still equals `10 ^ scale`, the ideal share
amount is the empty-vault formula: pricing an empty vault at `10 ^ scale` is
the special case of the general formula, not a different rule. -/
theorem Vault.idealSharesDeposit_initial_rate (v : Vault) (amount : ℚ)
    -- the starting vault is lawful
    (hrate : (v.toExact.sharesTotal : ℚ) = v.depositNav * (10 : ℚ) ^ v.scale.toNat) :
    v.idealSharesDeposit amount = amount * (10 : ℚ) ^ v.scale.toNat :=
  Vault.idealSharesDeposit_initial_rate_proof v amount hrate

/-- A larger rounded amount never buys fewer shares from the same vault. -/
theorem Vault.deposit_shares_monotone (v : Vault)
    -- the starting vault is lawful
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount)
    (r₁ r₂ : DepositResult)
    -- both rounded amounts are stored canonically and are positive
    (hcanon₁ : roundedAmount₁.Canonical) (hcanon₂ : roundedAmount₂.Canonical)
    (hposR₁ : 0 < roundedAmount₁.toRat) (hposR₂ : 0 < roundedAmount₂.toRat)
    -- both amounts round to a nonzero roundedAmount
    (hrounded₁ : v.roundedDepositAmount amountDeposit₁ = .ok (.rounded roundedAmount₁))
    (hrounded₂ : v.roundedDepositAmount amountDeposit₂ = .ok (.rounded roundedAmount₂))
    -- both deposits succeed, each starting from the same vault v.toRawVault
    (hok₁ : v.deposit amountDeposit₁ false = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : v.deposit amountDeposit₂ false = .ok r₂) (herr₂ : r₂.error = none)
    -- the first rounded amount is at most the second
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    -- the first deposit is issued at most as many shares
    r₁.sharesIssued.toRat ≤ r₂.sharesIssued.toRat :=
  Vault.deposit_shares_monotone_proof v amountDeposit₁ amountDeposit₂
    roundedAmount₁ roundedAmount₂ r₁ r₂ hcanon₁ hcanon₂ hposR₁ hposR₂
    hrounded₁ hrounded₂ hok₁ herr₁ hok₂ herr₂ hle

/-- Issued shares are a nonnegative integer matching `idealSharesDeposit` of
`roundedAmount` up to the `Number` stage error and the final truncation: at
most `depositε` relatively above, less than one whole share plus `depositε`
below. -/
theorem Vault.deposit_sharesIssued (v : Vault) (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : roundedAmount.Canonical) -- the rounded amount is stored canonically
    (hpos : 0 < roundedAmount.toRat) -- the rounded amount is positive, the preflight guard
    -- the net asset value clears the deep-underflow threshold of the Number line
    (hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.sharesIssued.toRat.den = 1 ∧ 0 ≤ r.sharesIssued.toRat ∧
    v.idealSharesDeposit roundedAmount.toRat * (1 - depositε) - 1 < r.sharesIssued.toRat ∧
    r.sharesIssued.toRat ≤ v.idealSharesDeposit roundedAmount.toRat * (1 + depositε) :=
  Vault.deposit_sharesIssued_proof v amountDeposit roundedAmount r hcanon hpos hnav
    hrounded hok herr

/-- Witness: the truncation term in `deposit_sharesIssued` cannot be dropped, a
run exists whose share error exceeds the relative `depositε` bound alone. -/
theorem Vault.deposit_sharesIssued_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesIssued
        (v.idealSharesDeposit roundedAmount.toRat) depositε :=
  Vault.deposit_sharesIssued_witness

/-- The exchange charge is the raw `computeDeposit` result. The returned taken
amount is the later posterior-total clamp, so this contract exposes the raw witness
and carries its exact `raw - final` clamp-rounding correction into the final-return
bounds. The final asset itself remains the value used for returned/state-update facts. -/
theorem Vault.deposit_charge (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    ∃ rawAssetDeposited : STAmount,
      clampToSumExponent v.assetsTotal rawAssetDeposited = .ok r.amountDeposit' ∧
      rawAssetDeposited.toRat ≤ amountDeposit.toRat ∧
      (rawAssetDeposited.isZero = false →
        v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) ≤
          r.amountDeposit'.toRat +
            (rawAssetDeposited.toRat - r.amountDeposit'.toRat)) ∧
      (rawAssetDeposited.isZero = true →
        v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) <
          if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) ∧
      (rawAssetDeposited.isZero = false →
        r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
          v.idealChargeDeposit r.sharesIssued.toRat * depositε +
            2 * (10 : ℚ) ^ rawAssetDeposited.exponent -
              (rawAssetDeposited.toRat - r.amountDeposit'.toRat)) :=
  Vault.deposit_charge_proof v amountDeposit r hcanon hpos hok herr

/-- Witness: the ULP term in `deposit_charge` cannot be dropped, a run exists
whose taken amount misses the exact share value by more than `depositε`
relative. -/
theorem Vault.deposit_charge_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.amountDeposit'
        (v.idealChargeDeposit r.sharesIssued.toRat) depositε :=
  Vault.deposit_charge_witness

/-- Integral strengthening of `deposit_charge`: the overcharge stays below
one whole unit plus the stage error. -/
theorem Vault.deposit_charge_integral (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      1 + v.idealChargeDeposit r.sharesIssued.toRat * depositε :=
  Vault.deposit_charge_integral_proof v amountDeposit r hcanon hint hpos hok herr

/-- A successful deposit exposes the exact final clamped asset `Number` used by
both asset additions and the exact issued-share `Number` used by the share
addition. This is the source-faithful state-wiring contract: raw
`computeDeposit` assets are not reused as state deltas. -/
theorem Vault.deposit_vault_updates (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) (herr : r.error = none) :
    ∃ cN : Number,
      r.amountDeposit'.toNumber .to_nearest = .ok cN ∧
      v.assetsTotal.operator_add cN .to_nearest = .ok r.vault'.assetsTotal ∧
      v.assetsAvailable.operator_add cN .to_nearest = .ok r.vault'.assetsAvailable ∧
      ∃ sN : Number,
        r.sharesIssued.toNumber .to_nearest = .ok sN ∧
        v.sharesTotal.operator_add sN .to_nearest = .ok r.vault'.sharesTotal :=
  Vault.deposit_vault_updates_proof v amountDeposit isDonation hcanon hpos r hok herr

/-- Witness: the error term in `deposit_vault_updates` cannot be dropped, a run
exists where the stored total is not the exact sum. The int64 witness `wvDVU`
donates `9000000000000000006`; the stored total `18000000000000000010` differs
from the exact sum `18000000000000000013`. -/
theorem Vault.deposit_vault_updates_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (r : DepositResult),
      v.deposit amountDeposit isDonation = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal + r.amountDeposit'.toRat :=
  Vault.deposit_vault_updates_witness

/-- Witness: a real deposit can have a raw `computeDeposit` amount that differs
from the final amount after the source-faithful posterior-total clamp. The
witness keeps the raw computation and final stored amount distinct. -/
theorem Vault.deposit_clamp_rounding_attained :
    ∃ (v : Vault) (amountDeposit rawDeposit : STAmount) (r : DepositResult),
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      (match computeDeposit v amountDeposit with
        | .ok (.success assets _) => assets.operator_eq rawDeposit
        | _ => false) = true ∧
      clampToSumExponent v.assetsTotal rawDeposit = .ok r.amountDeposit' ∧
      rawDeposit.operator_eq r.amountDeposit' = false :=
  Vault.deposit_clamp_rounding_witness

/-- Witness: the final clamped deposit is the exact `Number` added to both
stored asset fields. This deliberately does not conflate the raw
`computeDeposit` amount with the state delta. -/
theorem Vault.deposit_final_deposit_updates_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
      (assetDeposited : Number),
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.amountDeposit'.toNumber .to_nearest = .ok assetDeposited ∧
      v.assetsTotal.operator_add assetDeposited .to_nearest = .ok r.vault'.assetsTotal ∧
      v.assetsAvailable.operator_add assetDeposited .to_nearest = .ok r.vault'.assetsAvailable :=
  Vault.deposit_final_deposit_updates_witness

/-- Integral strengthening of `deposit_vault_updates`: in-domain integer
sums are stored exactly. -/
theorem Vault.deposit_vault_updates_integral (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    -- the starting vault is lawful
    (r : DepositResult)
    (hnt : v.numericType = .int64 ∨ v.numericType = .native) -- the vault holds an integral asset
    (hcanon : amountDeposit.IntegralCanonical) -- an integral vault's amounts are integral
    (hty : amountDeposit.mNumericType = v.numericType) -- the deposit is in the vault's asset
    -- an integral vault's stored totals are integers
    (hdenA : v.assetsTotal.toRat.den = 1)
    (hdenAv : v.assetsAvailable.toRat.den = 1)
    (hok : v.deposit amountDeposit isDonation = .ok r) (herr : r.error = none)
    -- the new total fits the asset domain (int64)
    (hsz : v.toExact.assetsTotal + r.amountDeposit'.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal + r.amountDeposit'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable + r.amountDeposit'.toRat :=
  Vault.deposit_vault_updates_integral_proof v amountDeposit isDonation r hnt hcanon hty
    hdenA hdenAv hok herr hsz

/-- The maximum guard is excluded when the rounded donation path is under the
maximum and every real-deposit compute/clamp/accepted-precision prefix uses a
final asset Number whose actual post-addition guard is false. The latter is
explicit because the source clamps the raw exchange asset before conversion. -/
theorem Vault.deposit_under_maximum (v : Vault) (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hcanon : amountDeposit.Canonical)
    (hok : v.deposit amountDeposit isDonation = .ok r)
    (hmargin : ∀ m ∈ v.assetsMaximum,
      v.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat)
    (hfinalMax : ∀ (rawAssetDeposited assetDeposited sharesCreated : STAmount) (cN at' : Number),
      computeDeposit v roundedAmount = .ok (.success rawAssetDeposited sharesCreated) →
      clampToSumExponent v.assetsTotal rawAssetDeposited = .ok assetDeposited →
      assetDeposited.isFractionalNonPositive = .ok false →
      assetDeposited.toNumber .to_nearest = .ok cN →
      v.assetsTotal.operator_add cN .to_nearest = .ok at' →
      ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
        at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false) :
    r.error ≠ some .tecLIMIT_EXCEEDED :=
  Vault.deposit_under_maximum_proof v amountDeposit roundedAmount isDonation r hrounded
    hcanon hok hmargin hfinalMax

end XRPL.Model.SingleAssetVault
