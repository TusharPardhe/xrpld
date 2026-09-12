import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Model.Vault.VaultClawback

/-! # Clawback exit reductions

`computeClawback_codes` inventories every outcome of a `computeClawback` that
runs without a throw, and `Vault.clawback_error_codes_proof` walks every exit
of `Vault.clawback`. The walks use `bind_ok_peel`, `if`-elimination, and the
`tryCatch` step lemmas only, keeping the `checked`/`ofNumber` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeClawback` that runs without a throw. -/
theorem computeClawback_codes (v : Vault) (assets holderShares : STAmount)
    (cc : ComputeClawbackResult)
    (hok : computeClawback v assets holderShares = .ok cc) :
    cc.error = none ∨ cc.error = some .tecINTERNAL ∨ cc.error = some .tecPATH_DRY ∨
      cc.error = some .tecPRECISION_LOSS := by
  unfold computeClawback at hok
  simp only [] at hok
  by_cases hneg : assets.negative = true
  · rw [if_pos hneg] at hok
    injection hok with h
    rw [← h]
    exact .inr (.inl rfl)
  · rw [if_neg hneg] at hok
    simp only [pure_bind] at hok
    obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
    have handler_path_dry : ∀ (e : Error),
        tryCatch (Except.error e : Except Error (DoResultPR ComputeClawbackResult ComputeClawbackResult PUnit))
          (fun e => if isOverflow e = true then
              pure (DoResultPR.return (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
                STAmount.zero NumericType.int64⟩ : ComputeClawbackResult) PUnit.unit)
            else throw e >>= fun y => pure (DoResultPR.pure y PUnit.unit)) = Except.ok rr →
        cc.error = some .tecPATH_DRY := by
      intro e htc'
      rw [tryCatch_error] at htc'
      by_cases hov : isOverflow e = true
      · rw [if_pos hov, epure] at htc'
        rw [← Except.ok.inj htc'] at hK
        have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
            STAmount.zero NumericType.int64⟩ : ComputeClawbackResult) = Except.ok cc := hK
        rw [← Except.ok.inj hK2]
      · rw [if_neg hov, ethrow, err_bind] at htc'
        exact absurd htc' (by simp)
    cases hats : assetsToSharesClawback v assets holderShares with
    | error e =>
      rw [hats, err_bind] at htc
      exact .inr (.inr (.inl (handler_path_dry e htc)))
    | ok sd =>
      simp only [hats, ok_bind, epure] at htc
      cases hsa : v.sharesToAssetsWithdraw sd false with
      | error e2 =>
        rw [hsa, err_bind] at htc
        exact .inr (.inr (.inl (handler_path_dry e2 htc)))
      | ok ar =>
        simp only [hsa, ok_bind] at htc
        cases han : ar.toNumber .to_nearest with
        | error e3 =>
          rw [han, err_bind] at htc
          exact .inr (.inr (.inl (handler_path_dry e3 htc)))
        | ok arn =>
          simp only [han, ok_bind] at htc
          by_cases hgt : arn.operator_gt v.assetsAvailable = true
          · rw [if_pos hgt] at htc
            cases hof : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
            | error e4 =>
              rw [hof, err_bind] at htc
              exact .inr (.inr (.inl (handler_path_dry e4 htc)))
            | ok ar2 =>
              simp only [hof, ok_bind] at htc
              cases hats2 : assetsToSharesWithdraw v ar2 true false with
              | error e5 =>
                rw [hats2, err_bind] at htc
                exact .inr (.inr (.inl (handler_path_dry e5 htc)))
              | ok sd2 =>
                simp only [hats2, ok_bind] at htc
                cases hsa2 : v.sharesToAssetsWithdraw sd2 false with
                | error e6 =>
                  rw [hsa2, err_bind] at htc
                  exact .inr (.inr (.inl (handler_path_dry e6 htc)))
                | ok ar3 =>
                  simp only [hsa2, ok_bind] at htc
                  cases han2 : ar3.toNumber .to_nearest with
                  | error e7 =>
                    rw [han2, err_bind] at htc
                    exact .inr (.inr (.inl (handler_path_dry e7 htc)))
                  | ok arn3 =>
                    simp only [han2, ok_bind] at htc
                    by_cases hgt2 : arn3.operator_gt v.assetsAvailable = true
                    · rw [if_pos hgt2] at htc
                      rw [← Except.ok.inj htc] at hK
                      have hK2 : Except.ok (⟨some TER.tecINTERNAL, STAmount.zero v.numericType,
                          STAmount.zero NumericType.int64⟩ : ComputeClawbackResult) = Except.ok cc := hK
                      rw [← Except.ok.inj hK2]
                      exact .inr (.inl rfl)
                    · rw [if_neg hgt2] at htc
                      cases hclamp : clampToSumExponent v.assetsTotal ar3.operator_neg with
                      | error e8 =>
                        simp only [hclamp, err_bind] at htc
                        exact .inr (.inr (.inl (handler_path_dry e8 htc)))
                      | ok finalRecovered =>
                        simp only [hclamp, ok_bind] at htc
                        cases hprecision : finalRecovered.isFractionalNonPositive with
                        | error e9 =>
                          simp only [hprecision, err_bind] at htc
                          exact .inr (.inr (.inl (handler_path_dry e9 htc)))
                        | ok precision =>
                          simp only [hprecision, ok_bind] at htc
                          by_cases hp : precision = true
                          · rw [if_pos hp, tryCatch_ok] at htc
                            rw [← Except.ok.inj htc] at hK
                            have hK2 : Except.ok (⟨some TER.tecPRECISION_LOSS,
                                STAmount.zero v.numericType, STAmount.zero NumericType.int64⟩ :
                                ComputeClawbackResult) = Except.ok cc := hK
                            rw [← Except.ok.inj hK2]
                            exact .inr (.inr (.inr rfl))
                          · rw [if_neg hp, tryCatch_ok] at htc
                            rw [← Except.ok.inj htc] at hK
                            have hK2 : Except.ok (⟨none, finalRecovered, sd2⟩ : ComputeClawbackResult)
                                = Except.ok cc := hK
                            rw [← Except.ok.inj hK2]
                            exact .inl rfl
          · rw [if_neg hgt] at htc
            cases hclamp : clampToSumExponent v.assetsTotal ar.operator_neg with
            | error e8 =>
              simp only [hclamp, err_bind] at htc
              exact .inr (.inr (.inl (handler_path_dry e8 htc)))
            | ok finalRecovered =>
              simp only [hclamp, ok_bind] at htc
              cases hprecision : finalRecovered.isFractionalNonPositive with
              | error e9 =>
                simp only [hprecision, err_bind] at htc
                exact .inr (.inr (.inl (handler_path_dry e9 htc)))
              | ok precision =>
                simp only [hprecision, ok_bind] at htc
                by_cases hp : precision = true
                · rw [if_pos hp, tryCatch_ok] at htc
                  rw [← Except.ok.inj htc] at hK
                  have hK2 : Except.ok (⟨some TER.tecPRECISION_LOSS,
                      STAmount.zero v.numericType, STAmount.zero NumericType.int64⟩ :
                      ComputeClawbackResult) = Except.ok cc := hK
                  rw [← Except.ok.inj hK2]
                  exact .inr (.inr (.inr rfl))
                · rw [if_neg hp, tryCatch_ok] at htc
                  rw [← Except.ok.inj htc] at hK
                  have hK2 : Except.ok (⟨none, finalRecovered, sd⟩ : ComputeClawbackResult)
                      = Except.ok cc := hK
                  rw [← Except.ok.inj hK2]
                  exact .inl rfl

/-- Every outcome of a clawback that runs without a throw.

`tecINTERNAL` has two origins: a negative `assets` amount, and the check after
the recomputation against `assetsAvailable` (when the first computed recovery
exceeded `assetsAvailable`, the amount is recomputed from truncated shares,
and a recovery that still exceeds `assetsAvailable` returns `tecINTERNAL`).
xrpld excludes that second check from coverage as believed unreachable, but no
proof exists either way. TODO: prove the recomputation check dead on lawful
vaults if possible. Then for nonnegative `assets` this inventory loses
`tecINTERNAL`, and the matching xrpld check is certified removable. If instead
a lawful vault reaches it, that is a reportable xrpld bug. -/
theorem Vault.clawback_error_codes_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hok : v.clawback assets holderShares = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecPRECISION_LOSS := by
  unfold Vault.clawback at hok
  simp only [] at hok
  obtain ⟨result, hres, hok⟩ := bind_ok_peel _ _ _ hok
  have hcodes := computeClawback_codes v assets holderShares result hres
  by_cases h1 : result.error.isSome = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]
    rcases hcodes with hc | hc | hc | hc
    · exact .inl hc
    · exact .inr (.inl hc)
    · exact .inr (.inr (.inl hc))
    · exact .inr (.inr (.inr hc))
  · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
    by_cases h2 : result.sharesDestroyed.isZero = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]
      exact .inr (.inr (.inr rfl))
    · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
      obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨arn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h3 : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]
        exact .inr (.inr (.inr rfl))
      · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
        obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
        injection hok with h; rw [← h]
        exact .inl rfl

/-- **Proof body of `clawback_negative_amount`.** -/
theorem Vault.clawback_negative_amount_proof (v : Vault) (assets holderShares : STAmount)
    (hneg : assets.negative = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecINTERNAL) := by
  have hcc : computeClawback v assets holderShares =
      .ok ⟨some .tecINTERNAL, STAmount.zero v.numericType, STAmount.zero .int64⟩ := by
    unfold computeClawback
    simp only []
    rw [if_pos hneg]
    rfl
  unfold Vault.clawback
  simp only []
  rw [hcc, ok_bind]
  rfl

/-- **Proof body of `clawback_zero_shares`.** -/
theorem Vault.clawback_zero_shares_proof (v : Vault) (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecPRECISION_LOSS) := by
  unfold Vault.clawback
  simp only []
  rw [hcomp, ok_bind]
  rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [if_pos hz]
  rfl

/-- **Proof body of `clawback_recovery_too_small`.** -/
theorem Vault.clawback_recovery_too_small_proof (v : Vault) (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecPRECISION_LOSS) := by
  unfold Vault.clawback
  simp only []
  rw [hcomp, ok_bind]
  rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [if_neg (by rw [hz]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  simp only [hsN, haN, hat, hrt, hrt', ok_bind]
  rw [if_pos hguard]
  rfl

end XRPL.Model.SingleAssetVault
