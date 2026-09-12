import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Model.Vault.VaultWithdraw

/-! # Withdraw exit reductions

Code inventories for the two exchange computations (`computeWithdrawByAssets`,
`computeWithdrawByShares`) and the full `Vault.withdraw` walk behind
`withdraw_error_codes`. The walks use `bind_ok_peel`, `if`-elimination, and the
`tryCatch` step lemmas only, keeping the `checked`/`ofNumber` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeWithdrawByAssets` that runs without a throw. -/
theorem computeWithdrawByAssets_codes (v : Vault) (assets : STAmount) (waive : Bool)
    (cw : ComputeWithdrawResult) (hok : computeWithdrawByAssets v assets waive = .ok cw) :
    cw.error = none ∨ cw.error = some .tecPRECISION_LOSS ∨ cw.error = some .tecPATH_DRY := by
  unfold computeWithdrawByAssets at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  cases hats : assetsToSharesWithdraw v assets true waive with
  | error e =>
    rw [hats, err_bind, tryCatch_error] at htc
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
          STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
      rw [← Except.ok.inj hK2]
      exact .inr (.inr rfl)
    · rw [if_neg hov, ethrow, err_bind] at htc
      exact absurd htc (by simp)
  | ok shares =>
    simp only [hats, ok_bind, epure] at htc
    by_cases hz : shares.isZero = true
    · rw [if_pos hz, tryCatch_ok] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (⟨some TER.tecPRECISION_LOSS, STAmount.zero v.numericType,
          STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
      rw [← Except.ok.inj hK2]
      exact .inr (.inl rfl)
    · rw [if_neg hz] at htc
      cases hsa : v.sharesToAssetsWithdraw shares waive with
      | error e2 =>
        rw [hsa, err_bind, tryCatch_error] at htc
        by_cases hov : isOverflow e2 = true
        · rw [if_pos hov] at htc
          rw [← Except.ok.inj htc] at hK
          have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
              STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
          rw [← Except.ok.inj hK2]
          exact .inr (.inr rfl)
        · rw [if_neg hov, ethrow, err_bind] at htc
          exact absurd htc (by simp)
      | ok assets' =>
        simp only [hsa, ok_bind] at htc
        rw [tryCatch_ok] at htc
        rw [← Except.ok.inj htc] at hK
        have hK2 : Except.ok (⟨none, assets', shares⟩ : ComputeWithdrawResult)
            = Except.ok cw := hK
        rw [← Except.ok.inj hK2]
        exact .inl rfl

/-- Every outcome of a `computeWithdrawByShares` that runs without a throw. -/
theorem computeWithdrawByShares_codes (v : Vault) (shares : STAmount) (waive : Bool)
    (cw : ComputeWithdrawResult) (hok : computeWithdrawByShares v shares waive = .ok cw) :
    cw.error = none ∨ cw.error = some .tecPATH_DRY := by
  unfold computeWithdrawByShares at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  cases hsa : v.sharesToAssetsWithdraw shares waive with
  | error e =>
    rw [hsa, err_bind, tryCatch_error] at htc
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
          STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
      rw [← Except.ok.inj hK2]
      exact .inr rfl
    · rw [if_neg hov, ethrow, err_bind] at htc
      exact absurd htc (by simp)
  | ok assets =>
    simp only [hsa, ok_bind, epure] at htc
    rw [tryCatch_ok] at htc
    rw [← Except.ok.inj htc] at hK
    have hK2 : Except.ok (⟨none, assets, shares⟩ : ComputeWithdrawResult)
        = Except.ok cw := hK
    rw [← Except.ok.inj hK2]
    exact .inl rfl

/-- Every outcome of a withdrawal that runs without a throw. -/
theorem Vault.withdraw_error_codes_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.error = none ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecINSUFFICIENT_FUNDS ∨
    r.error = some .tefINTERNAL := by
  unfold Vault.withdraw at hok
  simp only [] at hok
  cases amount
  case' vaultAssets a =>
    simp only [] at hok
    obtain ⟨result, hres, hok⟩ := bind_ok_peel _ _ _ hok
    have hcodes : result.error = none ∨ result.error = some .tecPRECISION_LOSS ∨
        result.error = some .tecPATH_DRY :=
      computeWithdrawByAssets_codes v a waiveUnrealizedLoss result hres
    clear hres
  case' vaultShares s =>
    simp only [] at hok
    obtain ⟨result, hres, hok⟩ := bind_ok_peel _ _ _ hok
    have hcodes : result.error = none ∨ result.error = some .tecPRECISION_LOSS ∨
        result.error = some .tecPATH_DRY :=
      (computeWithdrawByShares_codes v s waiveUnrealizedLoss result hres).elim Or.inl
        (fun hc => Or.inr (Or.inr hc))
    clear hres
  all_goals {
    by_cases h1 : result.error.isSome = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]
      rcases hcodes with hc | hc | hc
      · exact .inl hc
      · exact .inr (.inl hc)
      · exact .inr (.inr (.inl hc))
    · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
      obtain ⟨assetsNumber', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h2 : v.assetsAvailable.operator_lt assetsNumber' = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]
        exact .inr (.inr (.inr (.inl rfl)))
      · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
        obtain ⟨sta, _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h3 : result.sharesRedeemed.operator_eq sta = true
        · rw [if_pos h3] at hok
          by_cases h4 : v.lossUnrealized.operator_ne Number.zero = true
          · rw [if_pos h4] at hok; injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr rfl)))
          · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
            obtain ⟨allAvail, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]; exact .inl rfl
        · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
          obtain ⟨assetDebited, _, hok⟩ := bind_ok_peel _ _ _ hok
          cases hprecision : assetDebited.isFractionalNonPositive with
          | error e =>
            rw [hprecision, err_bind] at hok
            exact absurd hok (by simp)
          | ok isFractionalNonPositive =>
            simp only [hprecision, ok_bind] at hok
            by_cases hprecision' : isFractionalNonPositive = true
            · rw [if_pos hprecision'] at hok; injection hok with h; rw [← h]
              exact .inr (.inl rfl)
            · rw [if_neg hprecision'] at hok
              obtain ⟨assetsNumber'', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨sbn, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
              by_cases h5 : (assetsNumber''.mantissa_ != 0 && atr.operator_eq atr') = true
              · rw [if_pos h5] at hok; injection hok with h; rw [← h]
                exact .inr (.inl rfl)
              · rw [if_neg h5] at hok; try simp only [pure_bind] at hok
                obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
                injection hok with h; rw [← h]; exact .inl rfl
  }

/-- **Proof body of `sharesToAssetsWithdraw_zero_nav`.** -/
theorem Vault.sharesToAssetsWithdraw_zero_nav_proof (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
    (hnav : v.assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok netAssetValue)
    (hz : netAssetValue.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares waiveUnrealizedLoss =
      .ok (STAmount.zero v.numericType) := by
  cases waiveUnrealizedLoss
  all_goals {
    unfold Vault.sharesToAssetsWithdraw
    simp only []
    rw [hnav, ok_bind]
    rw [if_pos (beq_iff_eq.mpr hz)]
    rfl
  }

/-- **Proof body of `withdraw_insufficient_funds`.** -/
theorem Vault.withdraw_insufficient_funds_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = true) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected v .tecINSUFFICIENT_FUNDS) := by
  unfold Vault.withdraw
  simp only []
  cases amount
  all_goals {
    simp only [] at hcomp ⊢
    rw [hcomp, ok_bind]
    rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [haN, ok_bind, if_pos hins]
    rfl
  }

/-- **Proof body of `withdraw_final_nonzero_loss`.** -/
theorem Vault.withdraw_final_nonzero_loss_proof (v : Vault) (amount : WithdrawAmount)
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
      .ok (.rejected v .tefINTERNAL) := by
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
    rw [hst, ok_bind, if_pos hfin, if_pos hloss]
    rfl
  }

/-- **Proof body of `withdraw_payout_too_small`.

`cw.assets'` prices the requested payout for the availability guard.  A
non-final withdrawal then clamps its negation to the stored-total scale and
uses that transformed amount for the precision guard and every state update. -/
theorem Vault.withdraw_payout_too_small_proof (v : Vault) (amount : WithdrawAmount)
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
      .ok (.rejected v .tecPRECISION_LOSS) := by
  unfold Vault.withdraw
  simp only []
  cases amount
  all_goals {
    simp only [] at hcomp ⊢
    rw [hcomp, ok_bind]
    rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hraw, ok_bind, if_neg (by rw [hins]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hst, ok_bind, if_neg (by rw [hfin]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hclamp, ok_bind, hprecision, ok_bind]
    rw [if_neg Bool.false_ne_true]
    simp only [haN, hsN, hat, hrt, hrt', ok_bind]
    rw [if_pos hguard]
    rfl
  }

end XRPL.Model.SingleAssetVault
