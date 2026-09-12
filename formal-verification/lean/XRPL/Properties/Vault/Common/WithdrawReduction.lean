import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.DepositReduction

/-! # Guard-extraction reductions for `Vault.withdraw`

The accuracy proofs need to recover, from a successful run
(`v.withdraw … = .ok r` with `r.error = none`), every intermediate the success
record was built from. This file provides that walk for the withdraw pipeline:
the two exchange helpers (`sharesToAssetsWithdraw`, `assetsToSharesWithdraw`),
the two `computeWithdrawBy*` wrappers (whose `try`/`catch` handler can only
produce error codes), and `Vault.withdraw` itself, split into its final and
non-final success exits.

The walk uses only `bind_ok_peel` and `if`-elimination, so every heavy step
stays an opaque `.ok` witness and the well-founded `Number` pipeline is never
forced. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `STAmount.zero` basics -/

/-- The canonical zero amount is flagged zero. -/
theorem STAmount.zero_isZero (nt : NumericType) : (STAmount.zero nt).isZero = true := by
  cases nt with
  | fractional => rfl
  | integral mv mo ms msh => rfl

/-- The canonical zero amount stores mantissa `0`. -/
theorem STAmount.zero_mValue (nt : NumericType) : (STAmount.zero nt).mValue = 0 := by
  cases nt with
  | fractional => rfl
  | integral mv mo ms msh => rfl

/-- The canonical zero amount is sign-cleared. -/
theorem STAmount.zero_mIsNegative (nt : NumericType) :
    (STAmount.zero nt).mIsNegative = false := by
  cases nt with
  | fractional => rfl
  | integral mv mo ms msh => rfl

/-- The canonical zero amount has value zero. -/
theorem STAmount.zero_toRat (nt : NumericType) : (STAmount.zero nt).toRat = 0 := by
  rw [STAmount.toRat_of_nonneg _ (STAmount.zero_mIsNegative nt), STAmount.zero_mValue]
  norm_num

/-! ## `Vault.sharesToAssetsWithdraw` -/

/-- **`sharesToAssetsWithdraw` success reduction.** Exposes the pricing
subtraction, then either the zero-NAV early exit or the full
`toNumber`/`operator_mul`/`operator_div`/`ofNumber` chain. -/
theorem Vault.sharesToAssetsWithdraw_ok_reduces (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    ∃ nav : Number,
      v.assetsTotal.operator_sub
        (match waiveUnrealizedLoss with
          | true => Number.zero
          | false => v.lossUnrealized) .to_nearest = .ok nav ∧
      ((nav.mantissa_ = 0 ∧ assets = STAmount.zero v.numericType) ∨
       (nav.mantissa_ ≠ 0 ∧ ∃ sharesNumber NAVShares assetsNumber : Number,
         shares.toNumber .to_nearest = .ok sharesNumber ∧
         nav.operator_mul sharesNumber .to_nearest = .ok NAVShares ∧
         NAVShares.operator_div v.sharesTotal .to_nearest = .ok assetsNumber ∧
         STAmount.ofNumber v.numericType assetsNumber .downward = .ok assets)) := by
  cases waiveUnrealizedLoss <;>
  · unfold Vault.sharesToAssetsWithdraw at hok
    simp only [pure_bind, bind_pure] at hok
    obtain ⟨nav, h1, hok⟩ := bind_ok_peel _ _ _ hok
    refine ⟨nav, h1, ?_⟩
    by_cases hz : (nav.mantissa_ == 0) = true
    · rw [if_pos hz] at hok
      exact Or.inl ⟨beq_iff_eq.mp hz, (Except.ok.inj hok).symm⟩
    · rw [if_neg hz] at hok
      obtain ⟨sn, hsn, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨nv, hnv, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨an, han, hok⟩ := bind_ok_peel _ _ _ hok
      exact Or.inr ⟨by simpa using hz, sn, nv, an, hsn, hnv, han, hok⟩

/-! ## `assetsToSharesWithdraw` -/

/-- **`assetsToSharesWithdraw` success reduction.** Same pricing subtractions,
then either the zero-NAV early exit or the mirrored
`toNumber`/`operator_mul`/`operator_div`/(optional truncate)/`ofNumber` chain. -/
theorem assetsToSharesWithdraw_ok_reduces (v : Vault) (assets shares : STAmount)
    (truncateShares waiveUnrealizedLoss : Bool)
    (hok : assetsToSharesWithdraw v assets truncateShares waiveUnrealizedLoss = .ok shares) :
    ∃ nav : Number,
      v.assetsTotal.operator_sub
        (match waiveUnrealizedLoss with
          | true => Number.zero
          | false => v.lossUnrealized) .to_nearest = .ok nav ∧
      ((nav.mantissa_ = 0 ∧ shares = STAmount.zero .int64) ∨
       (nav.mantissa_ ≠ 0 ∧ ∃ assetsNumber sharesAssets sharesNumber sharesNumber' : Number,
         assets.toNumber .to_nearest = .ok assetsNumber ∧
         v.sharesTotal.operator_mul assetsNumber .to_nearest = .ok sharesAssets ∧
         sharesAssets.operator_div nav .to_nearest = .ok sharesNumber ∧
         (match truncateShares with
           | true => sharesNumber.truncate
           | false => pure sharesNumber) = .ok sharesNumber' ∧
         STAmount.ofNumber .int64 sharesNumber' .to_nearest = .ok shares)) := by
  cases truncateShares <;> cases waiveUnrealizedLoss <;>
  · unfold assetsToSharesWithdraw at hok
    simp only [pure_bind] at hok
    obtain ⟨nav, h1, hok⟩ := bind_ok_peel _ _ _ hok
    refine ⟨nav, h1, ?_⟩
    by_cases hz : (nav.mantissa_ == 0) = true
    · rw [if_pos hz] at hok
      exact Or.inl ⟨beq_iff_eq.mp hz, (Except.ok.inj hok).symm⟩
    · rw [if_neg hz] at hok
      obtain ⟨an, han, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨sa, hsa, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨sn, hsn, hok⟩ := bind_ok_peel _ _ _ hok
      first
        | exact Or.inr ⟨by simpa using hz, an, sa, sn, sn, han, hsa, hsn, rfl, hok⟩
        | · obtain ⟨sn', hsn', hok⟩ := bind_ok_peel _ _ _ hok
            exact Or.inr ⟨by simpa using hz, an, sa, sn, sn', han, hsa, hsn, hsn', hok⟩

/-! ## `computeWithdrawByShares` / `computeWithdrawByAssets` -/

/-- **`computeWithdrawByShares` no-error reduction.** The `try`/`catch` handler
can only produce error codes, so a `cw.error = none` outcome forces the body's
happy path: the pricing succeeded and the named shares are echoed. -/
theorem computeWithdrawByShares_none_reduces (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult)
    (hok : computeWithdrawByShares v shares waiveUnrealizedLoss = .ok cw)
    (herr : cw.error = none) :
    v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok cw.assets' ∧
    cw.sharesRedeemed = shares := by
  unfold computeWithdrawByShares at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  cases hs : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss with
  | error e =>
    rw [hs, err_bind, tryCatch_error] at htc
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc
      rw [← Except.ok.inj htc] at hK
      have hcw := Except.ok.inj (show Except.ok _ = Except.ok cw from hK)
      rw [← hcw] at herr
      exact absurd herr (by simp)
    · rw [if_neg hov, ethrow, err_bind] at htc
      exact absurd htc (by simp)
  | ok assets =>
    rw [hs] at htc
    simp only [ok_bind, epure] at htc
    rw [tryCatch_ok] at htc
    rw [← Except.ok.inj htc] at hK
    have hcw := Except.ok.inj (show Except.ok _ = Except.ok cw from hK)
    rw [← hcw]
    exact ⟨rfl, rfl⟩

/-- **`computeWithdrawByAssets` no-error reduction.** A `cw.error = none`
outcome forces the body's happy path: the shares priced (nonzero), the payout
re-priced, both echoed in the record. -/
theorem computeWithdrawByAssets_none_reduces (v : Vault) (assets : STAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult)
    (hok : computeWithdrawByAssets v assets waiveUnrealizedLoss = .ok cw)
    (herr : cw.error = none) :
    ∃ shares : STAmount,
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok shares ∧
      shares.isZero = false ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok cw.assets' ∧
      cw.sharesRedeemed = shares := by
  unfold computeWithdrawByAssets at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  have handler_err : ∀ e : Error,
      tryCatch (Except.error e :
          Except Error (DoResultPR ComputeWithdrawResult ComputeWithdrawResult PUnit))
        (fun e => if isOverflow e = true then
            pure (DoResultPR.return
              ⟨some .tecPATH_DRY, STAmount.zero v.numericType, STAmount.zero .int64⟩
              PUnit.unit)
          else do
            let y ← throw e
            pure (DoResultPR.pure y PUnit.unit)) = .ok rr → False := by
    intro e htc'
    rw [tryCatch_error] at htc'
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc'
      rw [← Except.ok.inj htc'] at hK
      have hcw := Except.ok.inj (show Except.ok _ = Except.ok cw from hK)
      rw [← hcw] at herr
      exact absurd herr (by simp)
    · rw [if_neg hov, ethrow, err_bind] at htc'
      exact absurd htc' (by simp)
  cases hs : assetsToSharesWithdraw v assets true waiveUnrealizedLoss with
  | error e =>
    rw [hs, err_bind] at htc
    exact absurd htc (handler_err e)
  | ok shares =>
    rw [hs] at htc
    simp only [ok_bind, epure] at htc
    by_cases hz : shares.isZero = true
    · rw [if_pos hz, tryCatch_ok] at htc
      rw [← Except.ok.inj htc] at hK
      have hcw := Except.ok.inj (show Except.ok _ = Except.ok cw from hK)
      rw [← hcw] at herr
      exact absurd herr (by simp)
    · rw [if_neg hz] at htc
      cases hs2 : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss with
      | error e2 =>
        rw [hs2, err_bind] at htc
        exact absurd htc (handler_err e2)
      | ok assets' =>
        rw [hs2] at htc
        simp only [ok_bind] at htc
        rw [tryCatch_ok] at htc
        rw [← Except.ok.inj htc] at hK
        have hcw := Except.ok.inj (show Except.ok _ = Except.ok cw from hK)
        rw [← hcw]
        exact ⟨shares, rfl, by simpa using hz, hs2, rfl⟩

/-! ## `Vault.withdraw` -/

/-- **`Vault.withdraw` success reduction.** A run that returns no error code
exposes the raw helper payout used by the availability guard, and, for a
non-final withdrawal, the distinct clamped final debit.  The current model
clamps `-cw.assets'`, accepts its precision guard, then uses that final debit
for the returned amount and all stored-balance subtractions; no identity
between raw and final payout is assumed. -/
theorem Vault.withdraw_success_reduces (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none) :
    ∃ (cw : ComputeWithdrawResult) (rawAssetsNumber : Number) (sharesTotalAmount : STAmount),
      (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
        = .ok cw ∧
      cw.error = none ∧
      cw.assets'.toNumber .to_nearest = .ok rawAssetsNumber ∧
      v.assetsAvailable.operator_lt rawAssetsNumber = false ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned = cw.sharesRedeemed ∧
      ((cw.sharesRedeemed.operator_eq sharesTotalAmount = true ∧
        v.lossUnrealized.operator_ne Number.zero = false ∧
        ∃ allAvailable : STAmount,
          STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable ∧
          r.assets' = allAvailable ∧
          r.vault'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero }) ∨
       (cw.sharesRedeemed.operator_eq sharesTotalAmount = false ∧
        ∃ (sharesBurnedNumber assetDebitedNumber assetsTotal' assetsAvailable' sharesTotal' : Number)
          (assetDebited assetsTotalRounded assetsTotalRounded' : STAmount),
          cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber ∧
          clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok assetDebited ∧
          assetDebited.isFractionalNonPositive = .ok false ∧
          assetDebited.toNumber .to_nearest = .ok assetDebitedNumber ∧
          v.assetsTotal.operator_sub assetDebitedNumber .to_nearest = .ok assetsTotal' ∧
          STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded ∧
          STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded' ∧
          (assetDebitedNumber.mantissa_ != 0 &&
            assetsTotalRounded.operator_eq assetsTotalRounded') = false ∧
          v.assetsAvailable.operator_sub assetDebitedNumber .to_nearest = .ok assetsAvailable' ∧
          v.sharesTotal.operator_sub sharesBurnedNumber .to_nearest = .ok sharesTotal' ∧
          r.assets' = assetDebited ∧
          r.vault'.toRawVault = { v.toRawVault with assetsTotal := assetsTotal', assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' })) := by
  cases amount <;>
  · unfold Vault.withdraw at hok
    simp only [] at hok
    obtain ⟨cw, hcomp, hok⟩ := bind_ok_peel _ _ _ hok
    simp only [pure_bind] at hok
    by_cases he : cw.error.isSome = true
    · rw [if_pos he] at hok
      have hr := (Except.ok.inj hok).symm
      rw [hr] at herr
      have herr' : cw.error = none := herr
      rw [herr'] at he
      exact absurd he (by simp)
    · rw [if_neg he] at hok
      have herr2 : cw.error = none := by
        cases hce : cw.error with
        | none => rfl
        | some t => exact absurd (by rw [hce]; rfl) he
      obtain ⟨raw, hraw, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases hlt : v.assetsAvailable.operator_lt raw = true
      · rw [if_pos hlt] at hok
        have hr := (Except.ok.inj hok).symm
        rw [hr] at herr
        exact absurd herr (by simp [WithdrawResult.rejected])
      · rw [if_neg hlt] at hok
        obtain ⟨sta, hsta, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases hfin : cw.sharesRedeemed.operator_eq sta = true
        · rw [if_pos hfin] at hok
          by_cases hloss : v.lossUnrealized.operator_ne Number.zero = true
          · rw [if_pos hloss] at hok
            have hr := (Except.ok.inj hok).symm
            rw [hr] at herr
            exact absurd herr (by simp [WithdrawResult.rejected])
          · rw [if_neg hloss] at hok
            obtain ⟨aa, haa, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
            obtain rfl := Except.ok.inj hok
            exact ⟨cw, raw, sta, hcomp, herr2, hraw, by simpa using hlt, hsta, rfl,
              Or.inl ⟨hfin, by simpa using hloss, aa, haa, rfl, (RawVault.to_lawful_ok htl).1⟩⟩
        · rw [if_neg hfin] at hok
          obtain ⟨debited, hclamp, hok⟩ := bind_ok_peel _ _ _ hok
          cases hprecision : debited.isFractionalNonPositive with
          | error e =>
            rw [hprecision, err_bind] at hok
            exact absurd hok (by simp)
          | ok isFractionalNonPositive =>
            simp only [hprecision, ok_bind] at hok
            by_cases hprecision' : isFractionalNonPositive = true
            · rw [if_pos hprecision'] at hok
              have hr := (Except.ok.inj hok).symm
              rw [hr] at herr
              exact absurd herr (by simp [WithdrawResult.rejected])
            · rw [if_neg hprecision'] at hok
              have hprecisionFalse : isFractionalNonPositive = false := by
                simpa using hprecision'
              obtain ⟨debitNumber, hdebitNumber, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨sbn, hsbn, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨atr, hatr, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨atr', hatr', hok⟩ := bind_ok_peel _ _ _ hok
              by_cases hg : (debitNumber.mantissa_ != 0 && atr.operator_eq atr') = true
              · rw [if_pos hg] at hok
                have hr := (Except.ok.inj hok).symm
                rw [hr] at herr
                exact absurd herr (by simp [WithdrawResult.rejected])
              · rw [if_neg hg] at hok
                obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
                obtain rfl := Except.ok.inj hok
                exact ⟨cw, raw, sta, hcomp, herr2, hraw, by simpa using hlt, hsta, rfl,
                  Or.inr ⟨by simpa using hfin, sbn, debitNumber, at', av', st', debited, atr, atr',
                    hsbn, hclamp, by rw [← hprecisionFalse]; exact hprecision, hdebitNumber, hat,
                    hatr, hatr', by simpa using hg, hav, hst, rfl, (RawVault.to_lawful_ok htl).1⟩⟩

end XRPL.Model.SingleAssetVault
