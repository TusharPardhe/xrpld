import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.WithdrawReduction

/-! # Guard-extraction reductions for `Vault.clawback`

The clawback accuracy proofs recover, from a successful run
(`v.clawback … = .ok r` with `r.error = none`), every intermediate of the
`computeClawback` exchange (including the recompute-from-`assetsAvailable`
branch) and of the stored-field updates. Same discipline as
`WithdrawReduction`: `bind_ok_peel` plus `if`-elimination only. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- With a nonzero amount the clawback share computation is the withdraw one. -/
theorem assetsToSharesClawback_nonzero (v : Vault) (assets holderShares : STAmount)
    (hz : assets.isZero = false) :
    assetsToSharesClawback v assets holderShares =
      assetsToSharesWithdraw v assets true false := by
  unfold assetsToSharesClawback
  rw [if_neg (by rw [hz]; exact Bool.false_ne_true)]
  simp only [pure_bind]

/-- With a zero amount the clawback share computation returns the holder's
entire share balance unchanged. -/
theorem assetsToSharesClawback_zero (v : Vault) (assets holderShares : STAmount)
    (hz : assets.isZero = true) :
    assetsToSharesClawback v assets holderShares = .ok holderShares := by
  unfold assetsToSharesClawback
  rw [if_pos hz]
  rfl

/-- **`computeClawback` no-error reduction.** A `cr.error = none` outcome for a
nonzero amount forces the happy path of the body: the two-way exchange, and
either the computed recovery fit under `assetsAvailable`, or the clamped
recompute did. -/
theorem computeClawback_none_reduces (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult)
    (hz : assets.isZero = false)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    assets.negative = false ∧
    ∃ (sharesDestroyed rawAssetsRecovered finalAssetsRecovered : STAmount)
      (rawAssetsRecoveredNumber : Number),
      assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok rawAssetsRecovered ∧
      rawAssetsRecovered.toNumber .to_nearest = .ok rawAssetsRecoveredNumber ∧
      ((rawAssetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
        clampToSumExponent v.assetsTotal rawAssetsRecovered.operator_neg = .ok finalAssetsRecovered ∧
        finalAssetsRecovered.isFractionalNonPositive = .ok false ∧
        cr.assetsRecovered = finalAssetsRecovered ∧ cr.sharesDestroyed = sharesDestroyed) ∨
       (rawAssetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
        ∃ (clamped sharesDestroyed' rawAssetsRecovered' finalAssetsRecovered' : STAmount)
          (rawAssetsRecoveredNumber' : Number),
          STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok clamped ∧
          assetsToSharesWithdraw v clamped true false = .ok sharesDestroyed' ∧
          v.sharesToAssetsWithdraw sharesDestroyed' false = .ok rawAssetsRecovered' ∧
          rawAssetsRecovered'.toNumber .to_nearest = .ok rawAssetsRecoveredNumber' ∧
          rawAssetsRecoveredNumber'.operator_gt v.assetsAvailable = false ∧
          clampToSumExponent v.assetsTotal rawAssetsRecovered'.operator_neg = .ok finalAssetsRecovered' ∧
          finalAssetsRecovered'.isFractionalNonPositive = .ok false ∧
          cr.assetsRecovered = finalAssetsRecovered' ∧ cr.sharesDestroyed = sharesDestroyed')) := by
  unfold computeClawback at hok
  simp only [pure_bind] at hok
  by_cases hneg : assets.negative = true
  · rw [if_pos hneg] at hok
    have hcr := (Except.ok.inj hok).symm
    rw [hcr] at herr
    exact absurd herr (by simp)
  · rw [if_neg hneg] at hok
    refine ⟨by simpa using hneg, ?_⟩
    obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
    rw [assetsToSharesClawback_nonzero v assets holderShares hz] at htc
    have handler_err : ∀ e : Error,
        tryCatch (Except.error e :
            Except Error (DoResultPR ComputeClawbackResult ComputeClawbackResult PUnit))
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
        have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
        rw [← hcr] at herr
        exact absurd herr (by simp)
      · rw [if_neg hov, ethrow, err_bind] at htc'
        exact absurd htc' (by simp)
    cases h1 : assetsToSharesWithdraw v assets true false with
    | error e => rw [h1, err_bind] at htc; exact absurd htc (handler_err e)
    | ok sharesDestroyed =>
      rw [h1] at htc
      simp only [ok_bind] at htc
      cases h2 : v.sharesToAssetsWithdraw sharesDestroyed false with
      | error e => rw [h2, err_bind] at htc; exact absurd htc (handler_err e)
      | ok assetsRecovered =>
        rw [h2] at htc
        simp only [ok_bind] at htc
        cases h3 : assetsRecovered.toNumber .to_nearest with
        | error e => rw [h3, err_bind] at htc; exact absurd htc (handler_err e)
        | ok arn =>
          rw [h3] at htc
          simp only [ok_bind] at htc
          by_cases hgt : arn.operator_gt v.assetsAvailable = true
          · rw [if_pos hgt] at htc
            cases h4 : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
            | error e => rw [h4, err_bind] at htc; exact absurd htc (handler_err e)
            | ok clamped =>
              rw [h4] at htc
              simp only [ok_bind] at htc
              cases h5 : assetsToSharesWithdraw v clamped true false with
              | error e => rw [h5, err_bind] at htc; exact absurd htc (handler_err e)
              | ok sharesDestroyed' =>
                rw [h5] at htc
                simp only [ok_bind] at htc
                cases h6 : v.sharesToAssetsWithdraw sharesDestroyed' false with
                | error e => rw [h6, err_bind] at htc; exact absurd htc (handler_err e)
                | ok assetsRecovered' =>
                  rw [h6] at htc
                  simp only [ok_bind] at htc
                  cases h7 : assetsRecovered'.toNumber .to_nearest with
                  | error e => rw [h7, err_bind] at htc; exact absurd htc (handler_err e)
                  | ok arn' =>
                    rw [h7] at htc
                    simp only [ok_bind] at htc
                    by_cases hgt' : arn'.operator_gt v.assetsAvailable = true
                    · rw [if_pos hgt', epure, tryCatch_ok] at htc
                      rw [← Except.ok.inj htc] at hK
                      have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                      rw [← hcr] at herr
                      exact absurd herr (by simp)
                    · rw [if_neg hgt'] at htc
                      cases hclamp : clampToSumExponent v.assetsTotal assetsRecovered'.operator_neg with
                      | error e =>
                          rw [hclamp, err_bind] at htc
                          exact absurd htc (handler_err e)
                      | ok finalAssetsRecovered =>
                          rw [hclamp] at htc
                          simp only [ok_bind] at htc
                          cases hprecision : finalAssetsRecovered.isFractionalNonPositive with
                          | error e =>
                              rw [hprecision, err_bind] at htc
                              exact absurd htc (handler_err e)
                          | ok precision =>
                              rw [hprecision] at htc
                              simp only [ok_bind] at htc
                              by_cases hprecision' : precision = true
                              · rw [if_pos hprecision', epure, tryCatch_ok] at htc
                                rw [← Except.ok.inj htc] at hK
                                have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                                rw [← hcr] at herr
                                exact absurd herr (by simp)
                              · rw [if_neg hprecision', epure, tryCatch_ok] at htc
                                rw [← Except.ok.inj htc] at hK
                                have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                                rw [← hcr]
                                exact ⟨sharesDestroyed, assetsRecovered, finalAssetsRecovered, arn,
                                  rfl, h2, h3,
                                  Or.inr ⟨hgt, clamped, sharesDestroyed', assetsRecovered',
                                    finalAssetsRecovered, arn', rfl, h5, h6, h7,
                                    by simpa using hgt', hclamp,
                                    by simpa [hprecision'] using hprecision, rfl, rfl⟩⟩
          · rw [if_neg hgt] at htc
            cases hclamp : clampToSumExponent v.assetsTotal assetsRecovered.operator_neg with
            | error e =>
                rw [hclamp, err_bind] at htc
                exact absurd htc (handler_err e)
            | ok finalAssetsRecovered =>
              rw [hclamp] at htc
              simp only [ok_bind] at htc
              cases hprecision : finalAssetsRecovered.isFractionalNonPositive with
            | error e =>
                rw [hprecision, err_bind] at htc
                exact absurd htc (handler_err e)
            | ok precision =>
                rw [hprecision] at htc
                simp only [ok_bind] at htc
                by_cases hprecision' : precision = true
                · rw [if_pos hprecision', epure, tryCatch_ok] at htc
                  rw [← Except.ok.inj htc] at hK
                  have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                  rw [← hcr] at herr
                  exact absurd herr (by simp)
                · rw [if_neg hprecision', epure, tryCatch_ok] at htc
                  rw [← Except.ok.inj htc] at hK
                  have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                  rw [← hcr]
                  exact ⟨sharesDestroyed, assetsRecovered, finalAssetsRecovered, arn, rfl, h2, h3,
                    Or.inl ⟨by simpa using hgt, hclamp,
                      by simpa [hprecision'] using hprecision, rfl, rfl⟩⟩

/-- **`computeClawback` no-error reduction, zero amount.** A `cr.error = none`
outcome for a zero amount destroys the holder's shares directly: the withdraw
prices `holderShares` through the withdraw pipeline, and either it fit under
`assetsAvailable` and the destroyed shares are exactly `holderShares`, or the
clamped recompute did. -/
theorem computeClawback_none_reduces_zero (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult)
    (hz : assets.isZero = true)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    assets.negative = false ∧
    ∃ (rawAssetsRecovered finalAssetsRecovered : STAmount)
      (rawAssetsRecoveredNumber : Number),
      v.sharesToAssetsWithdraw holderShares false = .ok rawAssetsRecovered ∧
      rawAssetsRecovered.toNumber .to_nearest = .ok rawAssetsRecoveredNumber ∧
      ((rawAssetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
        clampToSumExponent v.assetsTotal rawAssetsRecovered.operator_neg = .ok finalAssetsRecovered ∧
        finalAssetsRecovered.isFractionalNonPositive = .ok false ∧
        cr.assetsRecovered = finalAssetsRecovered ∧ cr.sharesDestroyed = holderShares) ∨
       (rawAssetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
        ∃ (clamped sharesDestroyed' rawAssetsRecovered' finalAssetsRecovered' : STAmount)
          (rawAssetsRecoveredNumber' : Number),
          STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok clamped ∧
          assetsToSharesWithdraw v clamped true false = .ok sharesDestroyed' ∧
          v.sharesToAssetsWithdraw sharesDestroyed' false = .ok rawAssetsRecovered' ∧
          rawAssetsRecovered'.toNumber .to_nearest = .ok rawAssetsRecoveredNumber' ∧
          rawAssetsRecoveredNumber'.operator_gt v.assetsAvailable = false ∧
          clampToSumExponent v.assetsTotal rawAssetsRecovered'.operator_neg = .ok finalAssetsRecovered' ∧
          finalAssetsRecovered'.isFractionalNonPositive = .ok false ∧
          cr.assetsRecovered = finalAssetsRecovered' ∧ cr.sharesDestroyed = sharesDestroyed')) := by
  unfold computeClawback at hok
  simp only [pure_bind] at hok
  by_cases hneg : assets.negative = true
  · rw [if_pos hneg] at hok
    have hcr := (Except.ok.inj hok).symm
    rw [hcr] at herr
    exact absurd herr (by simp)
  · rw [if_neg hneg] at hok
    refine ⟨by simpa using hneg, ?_⟩
    obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
    rw [assetsToSharesClawback_zero v assets holderShares hz] at htc
    have handler_err : ∀ e : Error,
        tryCatch (Except.error e :
            Except Error (DoResultPR ComputeClawbackResult ComputeClawbackResult PUnit))
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
        have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
        rw [← hcr] at herr
        exact absurd herr (by simp)
      · rw [if_neg hov, ethrow, err_bind] at htc'
        exact absurd htc' (by simp)
    simp only [ok_bind] at htc
    cases h2 : v.sharesToAssetsWithdraw holderShares false with
    | error e => rw [h2, err_bind] at htc; exact absurd htc (handler_err e)
    | ok assetsRecovered =>
      rw [h2] at htc
      simp only [ok_bind] at htc
      cases h3 : assetsRecovered.toNumber .to_nearest with
      | error e => rw [h3, err_bind] at htc; exact absurd htc (handler_err e)
      | ok arn =>
        rw [h3] at htc
        simp only [ok_bind] at htc
        by_cases hgt : arn.operator_gt v.assetsAvailable = true
        · rw [if_pos hgt] at htc
          cases h4 : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
          | error e => rw [h4, err_bind] at htc; exact absurd htc (handler_err e)
          | ok clamped =>
            rw [h4] at htc
            simp only [ok_bind] at htc
            cases h5 : assetsToSharesWithdraw v clamped true false with
            | error e => rw [h5, err_bind] at htc; exact absurd htc (handler_err e)
            | ok sharesDestroyed' =>
              rw [h5] at htc
              simp only [ok_bind] at htc
              cases h6 : v.sharesToAssetsWithdraw sharesDestroyed' false with
              | error e => rw [h6, err_bind] at htc; exact absurd htc (handler_err e)
              | ok assetsRecovered' =>
                rw [h6] at htc
                simp only [ok_bind] at htc
                cases h7 : assetsRecovered'.toNumber .to_nearest with
                | error e => rw [h7, err_bind] at htc; exact absurd htc (handler_err e)
                | ok arn' =>
                  rw [h7] at htc
                  simp only [ok_bind] at htc
                  by_cases hgt' : arn'.operator_gt v.assetsAvailable = true
                  · rw [if_pos hgt', epure, tryCatch_ok] at htc
                    rw [← Except.ok.inj htc] at hK
                    have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                    rw [← hcr] at herr
                    exact absurd herr (by simp)
                  · rw [if_neg hgt'] at htc
                    cases hclamp : clampToSumExponent v.assetsTotal assetsRecovered'.operator_neg with
                    | error e =>
                        rw [hclamp, err_bind] at htc
                        exact absurd htc (handler_err e)
                    | ok finalAssetsRecovered =>
                      rw [hclamp] at htc
                      simp only [ok_bind] at htc
                      cases hprecision : finalAssetsRecovered.isFractionalNonPositive with
                    | error e =>
                        rw [hprecision, err_bind] at htc
                        exact absurd htc (handler_err e)
                    | ok precision =>
                        rw [hprecision] at htc
                        simp only [ok_bind] at htc
                        by_cases hprecision' : precision = true
                        · rw [if_pos hprecision', epure, tryCatch_ok] at htc
                          rw [← Except.ok.inj htc] at hK
                          have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                          rw [← hcr] at herr
                          exact absurd herr (by simp)
                        · rw [if_neg hprecision', epure, tryCatch_ok] at htc
                          rw [← Except.ok.inj htc] at hK
                          have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                          rw [← hcr]
                          exact ⟨assetsRecovered, finalAssetsRecovered, arn, rfl, h3,
                            Or.inr ⟨hgt, clamped, sharesDestroyed', assetsRecovered',
                              finalAssetsRecovered, arn', rfl, h5, h6, h7,
                              by simpa using hgt', hclamp,
                              by simpa [hprecision'] using hprecision, rfl, rfl⟩⟩
        · rw [if_neg hgt] at htc
          cases hclamp : clampToSumExponent v.assetsTotal assetsRecovered.operator_neg with
          | error e =>
              rw [hclamp, err_bind] at htc
              exact absurd htc (handler_err e)
          | ok finalAssetsRecovered =>
            rw [hclamp] at htc
            simp only [ok_bind] at htc
            cases hprecision : finalAssetsRecovered.isFractionalNonPositive with
          | error e =>
              rw [hprecision, err_bind] at htc
              exact absurd htc (handler_err e)
          | ok precision =>
              rw [hprecision] at htc
              simp only [ok_bind] at htc
              by_cases hprecision' : precision = true
              · rw [if_pos hprecision', epure, tryCatch_ok] at htc
                rw [← Except.ok.inj htc] at hK
                have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                rw [← hcr] at herr
                exact absurd herr (by simp)
              · rw [if_neg hprecision', epure, tryCatch_ok] at htc
                rw [← Except.ok.inj htc] at hK
                have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                rw [← hcr]
                exact ⟨assetsRecovered, finalAssetsRecovered, arn, rfl, h3,
                  Or.inl ⟨by simpa using hgt, hclamp,
                    by simpa [hprecision'] using hprecision, rfl, rfl⟩⟩

/-- **`Vault.clawback` success reduction.** A run that returns no error code
exposes the `computeClawback` result (nonzero destroyed shares), the passed
too-small guard, and the three stored-field updates in the success record. -/
theorem Vault.clawback_success_reduces (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ cr : ComputeClawbackResult,
      computeClawback v assets holderShares = .ok cr ∧ cr.error = none ∧
      cr.sharesDestroyed.isZero = false ∧
      r.assetsRecovered = cr.assetsRecovered ∧ r.sharesDestroyed = cr.sharesDestroyed ∧
      ∃ (sharesDestroyedNumber assetsRecoveredNumber
          assetsTotal' sharesTotal' assetsAvailable' : Number)
        (assetsTotalRounded assetsTotalRounded' : STAmount),
        cr.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber ∧
        cr.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
        v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok assetsTotal' ∧
        STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded ∧
        STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded' ∧
        (assetsRecoveredNumber.mantissa_ != 0 &&
          assetsTotalRounded.operator_eq assetsTotalRounded') = false ∧
        v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok sharesTotal' ∧
        v.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok assetsAvailable' ∧
        r.vault'.toRawVault = { v.toRawVault with sharesTotal := sharesTotal', assetsAvailable := assetsAvailable', assetsTotal := assetsTotal' } := by
  unfold Vault.clawback at hok
  simp only [] at hok
  obtain ⟨cr, hcomp, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [pure_bind] at hok
  by_cases he : cr.error.isSome = true
  · rw [if_pos he] at hok
    have hr := (Except.ok.inj hok).symm
    rw [hr] at herr
    have herr' : cr.error = none := herr
    rw [herr'] at he
    exact absurd he (by simp)
  · rw [if_neg he] at hok
    have herr2 : cr.error = none := by
      cases hce : cr.error with
      | none => rfl
      | some t => exact absurd (by rw [hce]; rfl) he
    by_cases hz : cr.sharesDestroyed.isZero = true
    · rw [if_pos hz] at hok
      have hr := (Except.ok.inj hok).symm
      rw [hr] at herr
      exact absurd herr (by simp [ClawbackResult.rejected])
    · rw [if_neg hz] at hok
      obtain ⟨sbn, hsbn, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨arn, harn, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr, hatr, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr', hatr', hok⟩ := bind_ok_peel _ _ _ hok
      by_cases hg : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
      · rw [if_pos hg] at hok
        have hr := (Except.ok.inj hok).symm
        rw [hr] at herr
        exact absurd herr (by simp [ClawbackResult.rejected])
      · rw [if_neg hg] at hok
        obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
        obtain rfl := Except.ok.inj hok
        exact ⟨cr, hcomp, herr2, by simpa using hz, rfl, rfl,
          sbn, arn, at', st', av', atr, atr', hsbn, harn, hat, hatr, hatr',
          by simpa using hg, hst, hav, (RawVault.to_lawful_ok htl).1⟩

/-- **Proof body of `clawback_zero_all_shares`.** The withdraw conversion is
raw; `computeClawback` commits its subsequently clamped, precision-accepted
negative recovery. -/
theorem Vault.clawback_zero_all_shares_proof (v : Vault)
    (assets holderShares rawAssetsRecovered finalAssetsRecovered : STAmount)
    (rawAssetsRecoveredNumber : Number) (r : ClawbackResult)
    (hz : assets.isZero = true)
    (hassets : v.sharesToAssetsWithdraw holderShares false = .ok rawAssetsRecovered)
    (hnum : rawAssetsRecovered.toNumber .to_nearest = .ok rawAssetsRecoveredNumber)
    (hle : rawAssetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hclamp : clampToSumExponent v.assetsTotal rawAssetsRecovered.operator_neg =
      .ok finalAssetsRecovered)
    (hprecision : finalAssetsRecovered.isFractionalNonPositive = .ok false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed = holderShares ∧ r.assetsRecovered = finalAssetsRecovered ∧
    holderShares.isZero = false := by
  obtain ⟨cr, hcomp, herr2, hcrnz, hra, hsd, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨-, raw, final, rawNumber, hraw, hrawNumber, hdisj⟩ :=
    computeClawback_none_reduces_zero v assets holderShares cr hz hcomp herr2
  have hraw_det : raw = rawAssetsRecovered := by
    rw [hassets] at hraw
    exact (Except.ok.inj hraw).symm
  have hnumber_det : rawNumber = rawAssetsRecoveredNumber := by
    rw [hraw_det, hnum] at hrawNumber
    exact (Except.ok.inj hrawNumber).symm
  rcases hdisj with ⟨-, hclamp', hprecision', hassets', hshares'⟩ | ⟨hgt, -⟩
  · have hfinal_det : final = finalAssetsRecovered := by
      rw [hraw_det, hclamp] at hclamp'
      exact (Except.ok.inj hclamp').symm
    have hprecision_det : final.isFractionalNonPositive = .ok false := by
      rw [hfinal_det]
      exact hprecision
    have hshares_det : r.sharesDestroyed = holderShares := hsd.trans hshares'
    have hassets_det : r.assetsRecovered = finalAssetsRecovered :=
      hra.trans (hassets'.trans hfinal_det)
    have hholder_nonzero : holderShares.isZero = false := by
      rw [← hshares']
      exact hcrnz
    exact ⟨hshares_det, hassets_det, hholder_nonzero⟩
  · rw [hnumber_det, hle] at hgt
    exact absurd hgt Bool.false_ne_true

end XRPL.Model.SingleAssetVault
