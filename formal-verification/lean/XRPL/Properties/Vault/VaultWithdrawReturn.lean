import XRPL.Properties.Vault.Common.WithdrawExits
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Common.Preservation

/-! # `Vault.withdraw` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `Vault.sharesToAssetsWithdraw` -/

/-- When assetsTotal minus lossUnrealized rounds to a zero mantissa, any `shares`
are paid exactly zero. This is the only early exit of `sharesToAssetsWithdraw`. -/
theorem Vault.sharesToAssetsWithdraw_zero_nav (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
    (hnav : v.assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok netAssetValue)
    (hz : netAssetValue.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares waiveUnrealizedLoss =
      .ok (STAmount.zero v.numericType) :=
  Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waiveUnrealizedLoss
    netAssetValue hnav hz

variable (v : Vault)

/-! ## `Vault.withdraw` -/

/-- The withdrawn amount `assets'` exceeds `assetsAvailable`: `some .tecINSUFFICIENT_FUNDS`. -/
theorem Vault.withdraw_insufficient_funds (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = true) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected v .tecINSUFFICIENT_FUNDS) :=
  Vault.withdraw_insufficient_funds_proof v amount waiveUnrealizedLoss cw assetsNumber'
    hcomp herr haN hins

/-- The withdrawal redeems the whole share total while `lossUnrealized` is
nonzero: `some .tefINTERNAL`. -/
theorem Vault.withdraw_final_nonzero_loss (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    (hloss : v.lossUnrealized.operator_ne Number.zero = true) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected v .tefINTERNAL) :=
  Vault.withdraw_final_nonzero_loss_proof v amount waiveUnrealizedLoss cw assetsNumber'
    sharesTotalAmount hcomp herr haN hins hst hfin hloss

/-- The withdrawal redeems the whole share total on a vault with no unrealized
loss: the vault is zeroed and the withdrawer is paid all of `assetsAvailable`.
The `to_lawful` re-check is proven to succeed via `withdraw_final_poststate_lawful`,
so the `.notLawful` throw is unreachable. -/
theorem Vault.withdraw_final (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount allAvailable : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    (hloss : v.lossUnrealized.operator_ne Number.zero = false)
    (hallAvail : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable) :
    ∃ v' : Vault,
      v.withdraw amount waiveUnrealizedLoss = .ok ⟨none, v', allAvailable, cw.sharesRedeemed⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  have hL : v.toExact.lossUnrealized = 0 :=
    (Number.operator_ne_zero_eq_false_iff v.lossUnrealized v.wf.lossUnrealized_norm).mp hloss
  obtain ⟨v', htl, hlv'eq⟩ := Vault.withdraw_final_poststate_lawful v hL
  refine ⟨v', ?_, hlv'eq⟩
  unfold Vault.withdraw
  simp only []
  cases amount
  all_goals {
    simp only [] at hcomp ⊢
    rw [hcomp, ok_bind]
    rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [haN, ok_bind, if_neg (by rw [hins]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hst, ok_bind, if_pos hfin,
      if_neg (by rw [hloss]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hallAvail, ok_bind, htl, ok_bind]
    rfl
  }

/-- A nonzero final clamped debit whose subtraction does not change
`assetsTotal` rounded into the vault's `numericType`: `some .tecPRECISION_LOSS`.
The raw payout is used only for the earlier availability guard. -/
theorem Vault.withdraw_payout_too_small (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult)
    (rawAssetsNumber assetsNumber' sharesBurnedNumber assetsTotal' : Number)
    (assetDebited sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (hraw : cw.assets'.toNumber .to_nearest = .ok rawAssetsNumber)
    (hins : v.assetsAvailable.operator_lt rawAssetsNumber = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hclamp : clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok assetDebited)
    (hprecision : assetDebited.isFractionalNonPositive = .ok false)
    (haN : assetDebited.toNumber .to_nearest = .ok assetsNumber')
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    (hat : v.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.withdraw_payout_too_small_proof v amount waiveUnrealizedLoss cw
    rawAssetsNumber assetsNumber' sharesBurnedNumber assetsTotal' assetDebited sharesTotalAmount
    assetsTotalRounded assetsTotalRounded' hcomp herr hraw hins hst hfin hclamp hprecision haN
    hsN hat hrt hrt' hguard

/-- Every guard passes on a non-final withdrawal: the stored total and available
assets each drop by the payout and the share total by the redeemed shares, the
post-state is still a `Vault`. -/
theorem Vault.withdraw_success (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult)
    (assetsNumber' sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' : Number)
    (assetDebitedFinal sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hp_norm : assetsNumber'.isNormalized) (hp_nn : 0 ≤ assetsNumber'.toRat)
    (hp_le : assetsNumber'.toRat ≤ v.assetsTotal.toRat)
    (hb_norm : sharesBurnedNumber.isNormalized) (hb_nn : 0 ≤ sharesBurnedNumber.toRat)
    (hb_den : sharesBurnedNumber.toRat.den = 1)
    (hb_le : sharesBurnedNumber.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hstn : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hclamp : clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok assetDebitedFinal)
    (hprecision : assetDebitedFinal.isFractionalNonPositive = .ok false)
    (haNfinal : assetDebitedFinal.toNumber .to_nearest = .ok assetsNumber')
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    (hat : v.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = false)
    (hav : v.assetsAvailable.operator_sub assetsNumber' .to_nearest = .ok assetsAvailable')
    (hshares : v.sharesTotal.operator_sub sharesBurnedNumber .to_nearest = .ok sharesTotal')
    (hempty : sharesTotal'.toRat = 0 → assetsTotal'.toRat = 0) :
    ∃ v' : Vault,
      v.withdraw amount waiveUnrealizedLoss = .ok ⟨none, v', assetDebitedFinal, cw.sharesRedeemed⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := assetsTotal', assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' } := by
  obtain ⟨v', htl, hlv'eq⟩ := Vault.withdraw_poststate_lawful v assetsNumber'
    sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' hL hAV hp_norm hp_nn hp_le
    hb_norm hb_nn hb_den hb_le hfit hat hav hshares hempty
  refine ⟨v', ?_, hlv'eq⟩
  unfold Vault.withdraw
  simp only []
  cases amount
  all_goals {
    simp only [] at hcomp ⊢
    rw [hcomp, ok_bind]
    rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [haN, ok_bind, if_neg (by rw [hins]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hstn, ok_bind, if_neg (by rw [hfin]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hclamp, ok_bind, hprecision, ok_bind,
      if_neg (by simp),
      haNfinal, ok_bind, hsN, ok_bind, hat, ok_bind, hrt, ok_bind, hrt', ok_bind]
    rw [if_neg (by rw [hguard]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hav, ok_bind, hshares, ok_bind, htl, ok_bind]
    rfl
  }

/-- Every outcome of a withdrawal that runs without a throw. -/
theorem Vault.withdraw_error_codes (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.error = none ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecINSUFFICIENT_FUNDS ∨
    r.error = some .tefINTERNAL :=
  Vault.withdraw_error_codes_proof v amount waiveUnrealizedLoss r hok

end XRPL.Model.SingleAssetVault
