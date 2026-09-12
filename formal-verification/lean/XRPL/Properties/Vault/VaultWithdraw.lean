import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Vault.Common.WithdrawWitness
import XRPL.Properties.Vault.Common.WithdrawMono

/-! # `Vault.withdraw` accuracy

Each `Number` stage of the withdraw exchange is correctly rounded within
`10 / (2 ^ 63 + 2)`, and under an exact pricing value no bound below composes
more than three stages, so the deposit budget `depositε = 10 ^ (-17)` covers
every composition and no separate withdraw constant is defined. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)


/-! ## `Vault.sharesToAssetsWithdraw` -/

/-- The returned amount is nonnegative, never exceeds the shares' worth by more than
`depositε` relatively, and when nonzero falls short of it by at most 2 ULP. The final
conversion rounds downward, marked "(waiting the C++ fix)" in the model, but
the interior stages round to nearest, so a plain upper bound by the worth
alone would be false. -/
theorem Vault.sharesToAssetsWithdraw_bounds (v : Vault) (shares assets : STAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    -- never pays more than the shares' worth, up to the stage error
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) ∧
    -- a nonzero returned amount underpays the shares' worth by at most the
    -- interior stage error plus 2 ULP (the other direction is already capped
    -- by the relative conjunct)
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε +
          2 * (10 : ℚ) ^ assets.exponent) :=
  Vault.sharesToAssetsWithdraw_bounds_proof v shares assets waiveUnrealizedLoss hnn hc hnav hok

/-- Witness: the ULP term in `sharesToAssetsWithdraw_bounds` cannot be
dropped, a run exists whose returned amount misses the shares' worth by more than
`depositε` relative. -/
theorem Vault.sharesToAssetsWithdraw_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      RoundsWithinWitness assets
        (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) depositε :=
  Vault.sharesToAssetsWithdraw_witness

/-- `sharesToAssetsWithdraw_bounds` without the `WithdrawNavExact` hypothesis,
so it also holds when computing assetsTotal minus lossUnrealized rounds. That
rounding moves the price of every share, and the
worst case is `navSlack * shares / sharesTotal`, which is added to both
bounds. When `WithdrawNavExact` holds, `sharesToAssetsWithdraw_bounds` gives
the tighter bounds without the slack term. -/
theorem Vault.sharesToAssetsWithdraw_total (v : Vault) (shares assets : STAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    -- never pays more than the shares' worth plus the slack, up to the stage error
    assets.toRat ≤
      (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ)) * (1 + depositε) ∧
    -- a nonzero payout falls short of the shares' worth by at most the slack
    -- plus 2 ULP
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ) * (1 + depositε) +
          2 * (10 : ℚ) ^ assets.exponent) :=
  Vault.sharesToAssetsWithdraw_total_proof v shares assets waiveUnrealizedLoss hnn hc hok

/-! ## `Vault.withdraw` -/

/-- A successful withdrawal that names shares burns exactly the named amount.
Error records report zero, the contract in `Unchanged.lean`. -/
theorem Vault.withdraw_sharesBurned_exact (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned = shares :=
  Vault.withdraw_sharesBurned_exact_proof v shares waiveUnrealizedLoss r hok herr

/-- Shares burned by an asset-denominated withdrawal are a positive integer
matching `idealSharesWithdraw` of the named `assets` up to the `Number` stage
error and the source-faithful truncation-to-whole-share step. -/
theorem Vault.withdraw_sharesBurned (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (r : WithdrawResult)
    (hpos : 0 < assets.toRat) -- the withdrawn amount is positive, the preflight guard
    (hc : assets.Canonical) -- assets stored canonically, so `assets.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned.toRat.den = 1 ∧ 0 < r.sharesBurned.toRat ∧
    |r.sharesBurned.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat| ≤
      1 + v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * depositε :=
  Vault.withdraw_sharesBurned_proof v assets waiveUnrealizedLoss r hpos hc hnav hok herr

/-- Witness: the half-share term in `withdraw_sharesBurned` cannot be dropped,
a run exists whose share error exceeds the relative `depositε` bound alone. -/
theorem Vault.withdraw_sharesBurned_attained :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      0 < assets.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesBurned
        (v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat) depositε :=
  Vault.withdraw_sharesBurned_witness

/- The `assets'` of a successful non-final withdrawal is nonnegative, never
exceeds the burned shares' worth by more than `depositε` relatively, and when
nonzero falls short of it by at most 2 ULP. Both `WithdrawAmount` forms share
this bound, the asset-denominated form derives the burned shares first. -/
/-- A non-final withdrawal exposes the raw exchange payout for price math, then
records the source-faithful clamped final debit for precision and state updates.
The price shortfall is transported to the final payout by the explicit clamp
term `|final - raw|`; no raw/final identity is assumed. -/
theorem Vault.withdraw_payout (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ rawPayout : STAmount,
      v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok rawPayout ∧
      clampToSumExponent v.assetsTotal rawPayout.operator_neg = .ok r.assets' ∧
      r.assets'.isFractionalNonPositive = .ok false ∧
      ∃ debitNumber assetsTotal' assetsAvailable' : Number,
        r.assets'.toNumber .to_nearest = .ok debitNumber ∧
        v.assetsTotal.operator_sub debitNumber .to_nearest = .ok assetsTotal' ∧
        v.assetsAvailable.operator_sub debitNumber .to_nearest = .ok assetsAvailable' ∧
        0 ≤ rawPayout.toRat ∧
        rawPayout.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) ∧
        (rawPayout.isZero = false →
          v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
            v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
              2 * (10 : ℚ) ^ rawPayout.exponent + |r.assets'.toRat - rawPayout.toRat|) :=
  Vault.withdraw_payout_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hnn hc hnav hok herr hst hfin

/-- Witness: the ULP term in `withdraw_payout` cannot be dropped, a run exists
whose `assets'` misses the burned shares' worth by more than `depositε`
relative. -/
theorem Vault.withdraw_payout_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      RoundsWithinWitness r.assets'
        (v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat) depositε :=
  Vault.withdraw_payout_witness

/- Integral strengthening of `withdraw_payout`: the shortfall stays below
one whole unit plus the stage error, with no nonzero condition. -/
/-- Integral non-final withdrawals retain the raw-price/final-debit provenance.
The clamp relation is explicit so clients cannot infer a false raw/final equality. -/
theorem Vault.withdraw_payout_integral (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ rawPayout : STAmount,
      v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok rawPayout ∧
      clampToSumExponent v.assetsTotal rawPayout.operator_neg = .ok r.assets' ∧
      r.assets'.isFractionalNonPositive = .ok false :=
  Vault.withdraw_payout_integral_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hint hnn hc hnav hok herr hst hfin

/-- More shares burned never decreases the **raw priced payout** from the same
vault.  A successful non-final withdrawal subsequently applies a dynamic,
post-sum-dependent clamp to this raw amount; raw and final amounts are not
interchangeable.  Final-debit monotonicity must additionally supply the
source-path post-sum/grid classifier evidence from `WithdrawPostSumMono` and
`WithdrawClampMono`. -/
theorem Vault.withdraw_raw_payout_monotone (v : Vault) (amount₁ amount₂ : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r₁ r₂ : WithdrawResult)
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    -- the burned shares are stored canonically and are nonnegative
    (hcb₁ : r₁.sharesBurned.Canonical) (hcb₂ : r₂.sharesBurned.Canonical)
    (hnnb₁ : 0 ≤ r₁.sharesBurned.toRat) (hnnb₂ : 0 ≤ r₂.sharesBurned.toRat)
    -- both withdrawals succeed, each starting from the same vault v.toRawVault
    (hok₁ : v.withdraw amount₁ waiveUnrealizedLoss = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : v.withdraw amount₂ waiveUnrealizedLoss = .ok r₂) (herr₂ : r₂.error = none)
    -- neither run is the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin₁ : r₁.sharesBurned.operator_eq sharesTotalAmount = false)
    (hfin₂ : r₂.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the first run burns at most as many shares
    (hle : r₁.sharesBurned.toRat ≤ r₂.sharesBurned.toRat) :
    ∃ raw₁ raw₂ : STAmount,
      v.sharesToAssetsWithdraw r₁.sharesBurned waiveUnrealizedLoss = .ok raw₁ ∧
      v.sharesToAssetsWithdraw r₂.sharesBurned waiveUnrealizedLoss = .ok raw₂ ∧
      raw₁.toRat ≤ raw₂.toRat :=
  Vault.withdraw_raw_payout_monotone_proof v amount₁ amount₂ waiveUnrealizedLoss
    sharesTotalAmount r₁ r₂ hnav hcb₁ hcb₂ hnnb₁ hnnb₂
    hok₁ herr₁ hok₂ herr₂ hst hfin₁ hfin₂ hle

/-- Final withdrawal debits are monotone once the two successful source paths
are classified. `WithdrawFinalDebitOrderEvidence` records the only valid
transports across the dynamic clamp: integral sign-clearing, a zero lower
output, or fractional post-sum grids (including their ordinary/cusp
classification). The raw payouts and final clamps are extracted from each
successful non-final withdrawal; this API never identifies `rawᵢ` with the
returned `rᵢ.assets'`. -/
theorem Vault.withdraw_final_debit_monotone_classified
    (v : Vault) (amount₁ amount₂ : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount)
    (r₁ r₂ : WithdrawResult)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hcb₁ : r₁.sharesBurned.Canonical) (hcb₂ : r₂.sharesBurned.Canonical)
    (hnnb₁ : 0 ≤ r₁.sharesBurned.toRat) (hnnb₂ : 0 ≤ r₂.sharesBurned.toRat)
    (hok₁ : v.withdraw amount₁ waiveUnrealizedLoss = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : v.withdraw amount₂ waiveUnrealizedLoss = .ok r₂) (herr₂ : r₂.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin₁ : r₁.sharesBurned.operator_eq sharesTotalAmount = false)
    (hfin₂ : r₂.sharesBurned.operator_eq sharesTotalAmount = false)
    (hle : r₁.sharesBurned.toRat ≤ r₂.sharesBurned.toRat)
    (hclassified : ∀ raw₁ raw₂ : STAmount,
      v.sharesToAssetsWithdraw r₁.sharesBurned waiveUnrealizedLoss = .ok raw₁ →
      v.sharesToAssetsWithdraw r₂.sharesBurned waiveUnrealizedLoss = .ok raw₂ →
      clampToSumExponent v.assetsTotal raw₁.operator_neg = .ok r₁.assets' →
      clampToSumExponent v.assetsTotal raw₂.operator_neg = .ok r₂.assets' →
      Vault.WithdrawFinalDebitOrderEvidence v raw₁ raw₂ r₁.assets' r₂.assets') :
    r₁.assets'.toRat ≤ r₂.assets'.toRat := by
  obtain ⟨raw₁, hprice₁, hclamp₁, _, _⟩ :=
    Vault.withdraw_payout v amount₁ waiveUnrealizedLoss sharesTotalAmount r₁
      hnnb₁ hcb₁ hnav hok₁ herr₁ hst hfin₁
  obtain ⟨raw₂, hprice₂, hclamp₂, _, _⟩ :=
    Vault.withdraw_payout v amount₂ waiveUnrealizedLoss sharesTotalAmount r₂
      hnnb₂ hcb₂ hnav hok₂ herr₂ hst hfin₂
  exact Vault.withdraw_final_debit_monotone_classified_proof v waiveUnrealizedLoss
    r₁.sharesBurned r₂.sharesBurned raw₁ raw₂ r₁.assets' r₂.assets'
    hcb₁ hcb₂ hnnb₁ hnnb₂ hnav hprice₁ hprice₂ hle hclamp₁ hclamp₂
    (hclassified raw₁ raw₂ hprice₁ hprice₂ hclamp₁ hclamp₂)

/- Both stored asset fields are the old value minus `assets'`, up to the
`depositε` relative error of the `Number` subtraction, and the share total
update is exact whenever the stored total fits the share domain. -/
/-- A non-final withdrawal converts its **final clamped debit** once and uses
that Number in every state subtraction. -/
theorem Vault.withdraw_vault_updates (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hpnn : 0 ≤ r.assets'.toRat) (hnn : 0 ≤ r.sharesBurned.toRat)
    (hc : r.sharesBurned.Canonical) (hSnt : r.sharesBurned.mNumericType = .int64)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ debitNumber sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' : Number,
      r.assets'.toNumber .to_nearest = .ok debitNumber ∧
      r.sharesBurned.toNumber .to_nearest = .ok sharesBurnedNumber ∧
      v.assetsTotal.operator_sub debitNumber .to_nearest = .ok assetsTotal' ∧
      v.assetsAvailable.operator_sub debitNumber .to_nearest = .ok assetsAvailable' ∧
      v.sharesTotal.operator_sub sharesBurnedNumber .to_nearest = .ok sharesTotal' :=
  Vault.withdraw_vault_updates_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hpnn hnn hc hSnt hok herr hst hfin

/-- Witness: a successful non-final withdrawal can change the raw share-price
result when it applies the source-faithful clamp. The final payout is exactly
the clamped amount, not the pre-clamp computation. -/
theorem Vault.withdraw_clamp_rounding_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (rawPayout : STAmount) (r : WithdrawResult),
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      (match amount with
        | .vaultAssets assets => do return (← computeWithdrawByAssets v assets waiveUnrealizedLoss).assets'
        | .vaultShares shares => do return (← computeWithdrawByShares v shares waiveUnrealizedLoss).assets') = .ok rawPayout ∧
      clampToSumExponent v.assetsTotal rawPayout.operator_neg = .ok r.assets' ∧
      rawPayout.operator_eq r.assets' = false :=
  Vault.withdraw_clamp_rounding_witness

/-- Witness: on the non-final path, the final payout is converted once to the
exact `Number` subtracted from both stored asset fields. This intentionally
makes no false claim that the raw pre-clamp payout differs from the state debit. -/
theorem Vault.withdraw_final_debit_updates_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult) (assetDebited : Number),
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      r.assets'.toNumber .to_nearest = .ok assetDebited ∧
      v.assetsTotal.operator_sub assetDebited .to_nearest = .ok r.vault'.assetsTotal ∧
      v.assetsAvailable.operator_sub assetDebited .to_nearest = .ok r.vault'.assetsAvailable :=
  Vault.withdraw_final_debit_updates_witness

/-- Integral withdrawal state-update accuracy. The raw payout is first clamped
into the final debit recorded in `assets'`; each stored balance is then the
correct-to-nearest result of subtracting that final debit. -/
theorem Vault.withdraw_vault_updates_integral (v : Vault) (amount : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assets'.toRat) -- a nonnegative payout, negative ones can leave the domain
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the stored total fits the asset domain (int64)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    ∃ (cw : ComputeWithdrawResult) (assetDebited : STAmount) (assetDebitedNumber : Number),
      (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss) = .ok cw ∧
      cw.error = none ∧
      clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok assetDebited ∧
      assetDebited.isFractionalNonPositive = .ok false ∧
      assetDebited.toNumber .to_nearest = .ok assetDebitedNumber ∧
      r.assets' = assetDebited ∧
      Number.RoundsToRepresentable r.vault'.assetsTotal
        (v.assetsTotal.toRat - r.assets'.toRat) .to_nearest ∧
      Number.RoundsToRepresentable r.vault'.assetsAvailable
        (v.assetsAvailable.toRat - r.assets'.toRat) .to_nearest :=
  Vault.withdraw_vault_updates_integral_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hint hok herr hnn hst hfin hsz

/- A successful non-final withdrawal with a positive `assets'` strictly decreases
the stored `assetsTotal` and never increases the stored `assetsAvailable`: the guard
rejecting an `assets'` too small to move the rounded `assetsTotal` guarantees the
total moved, and both fields subtract the same non-negative payout. The
`assetsAvailable` bound stays at `≤`: its strict decrease is a finer-grid
tie-exclusion the `assetsTotal` guard alone does not transfer. -/
/-- Positive non-final payouts expose the final debit Number and its two exact
state-subtraction equations. -/
theorem Vault.withdraw_payout_decreases_assets (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hc : r.sharesBurned.Canonical)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hpay : 0 < r.assets'.toRat)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    ∃ debitNumber assetsTotal' assetsAvailable' : Number,
      r.assets'.toNumber .to_nearest = .ok debitNumber ∧
      v.assetsTotal.operator_sub debitNumber .to_nearest = .ok assetsTotal' ∧
      v.assetsAvailable.operator_sub debitNumber .to_nearest = .ok assetsAvailable' :=
  Vault.withdraw_payout_decreases_assets_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hc hok herr hpay hst hfin

/-- The `assetsAvailable` guard compares the stored value against the rounded
amount, which can exceed the named shares' worth by the interior stage error.
A `depositε` relative margin under `assetsAvailable` absorbs every overshoot,
so the guard cannot fire. -/
theorem Vault.withdraw_under_available (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    -- the starting vault is lawful
    (hpos : 0 < shares.toRat) -- the withdrawn shares are positive, the preflight guard
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    -- the named shares' worth fits under assetsAvailable with margin
    (hmargin : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat *
      (1 + depositε) ≤ v.toExact.assetsAvailable) :
    -- the assetsAvailable guard cannot fire
    r.error ≠ some .tecINSUFFICIENT_FUNDS :=
  Vault.withdraw_under_available_proof v shares waiveUnrealizedLoss r hpos hc hnav hok hmargin


/-- A successful withdrawal empties the vault exactly when it burns the whole
share total: `sharesBurned` comparing equal to the stored share total is
equivalent to the result state having all three stored fields zero. A partial
burn always leaves a nonzero `sharesTotal'`, an over-burn a negative one. -/
theorem Vault.withdraw_final_iff (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) -- a positive burn (the meaningful by-shares input class)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical (used by the `←` direction)
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    r.sharesBurned.operator_eq sharesTotalAmount = true ↔
      r.vault'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } :=
  Vault.withdraw_final_iff_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hpos hc hSnt hok herr hst

/-- A final withdrawal pays all of `assetsAvailable`, and that amount obeys
the same bounds as a regular withdrawal of the same shares: at most the
shares' exact worth, at least the lower bound of `withdraw_payout`. It is
bounded on both sides because the computed amount passed the `assetsAvailable`
guard, and on a lawful vault `assetsAvailable` is at most the shares' exact
worth. -/
theorem Vault.withdraw_final_payout (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) -- a positive burn (the meaningful by-shares input class)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- the run was final: only the final branch zeroes the share total
    (hfinal : r.vault'.sharesTotal = Number.zero)
    -- `assetsAvailable` is representable at the vault's numeric type, so the final
    -- `ofNumber` pays exactly `assetsAvailable` and never rounds up past the shares'
    -- worth (holds on all reachable vaults; false on a Lawful-non-Reachable one)
    (hAAc : ∀ aa : STAmount,
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok aa →
        aa.toRat = v.assetsAvailable.toRat) :
    -- at most the whole share total's exact worth
    r.assets'.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat ∧
    -- with assets available to pay, at least what the regular accuracy window
    -- guarantees for the same shares. When no assets are available the final payout is
    -- the zero record, whose `mOffset` (`-100`) sits below the smallest representable
    -- grid, so its `2` ULP slack is too fine to cover the shares' worth and the lower
    -- bound is gated on a positive available balance
    (0 < v.toExact.assetsAvailable →
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 - depositε) -
        2 * (10 : ℚ) ^ r.assets'.exponent ≤ r.assets'.toRat) :=
  Vault.withdraw_final_payout_proof v amount waiveUnrealizedLoss r hpos hc hSnt hnav
    hok herr hfinal hAAc

-- `Vault.withdraw_can_empty` is FALSE as stated, so it is omitted rather than
-- assumed. A full-share redemption can hard-fail with `tecINSUFFICIENT_FUNDS`:
-- the interior to-nearest `mul`/`div` in `sharesToAssetsWithdraw` can overshoot
-- the priced payout by up to 1 ULP above `assetsAvailable`, and the funds guard
-- runs before the final-withdrawal branch, so it rejects the redemption. A sole
-- shareholder owning 100% of the vault can therefore be unable to exit in one
-- withdrawal even with nothing lent out. Confirmed by machine-checked witnesses
-- (see vault_bugs_confirmed.md). The former statement, for the record:
--
-- theorem Vault.withdraw_can_empty (sharesTotalAmount : STAmount)
--     (v.wf : v.WF) (v.exact : v.toExact.Valid)
--     (hlent : v.toExact.assetsTotal = v.toExact.assetsAvailable)
--     (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
--     ∃ allAvailable : STAmount,
--       STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable ∧
--       v.withdraw (.vaultShares sharesTotalAmount) false =
--         .ok ⟨none,
--           { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero,
--                    sharesTotal := Number.zero },
--           allAvailable, sharesTotalAmount⟩

end XRPL.Model.SingleAssetVault
