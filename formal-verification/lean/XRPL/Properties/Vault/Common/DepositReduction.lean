import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Protocol.STAmount.Compare.Compare

/-! # Guard-extraction reductions for `Vault.deposit`

The forward exit catalog (`VaultDepositReturn.lean`) proves "guard fired ⇒ code".
The accuracy proofs need the converse: from a successful run
(`v.deposit … = .ok r` with `r.error = none`) recover every intermediate the
success record was built from. This file provides that walk plus the
`computeDeposit` success reduction that exposes its internal `operator_gt` guard
(`amountDeposit' ≤ amountDeposit`).

The walk uses only `bind_ok_peel` and `if`-elimination, so every heavy step
(`toNumber`, `operator_add`, `computeDeposit`, `roundToVaultExponent`) stays an
opaque `.ok` witness and the `checked`/well-founded pipeline is never forced. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `tryCatch` on a success runs no handler, definitional. -/
theorem tryCatch_ok {ε α} (a : α) (h : ε → Except ε α) :
    (tryCatch (Except.ok a : Except ε α) h) = .ok a := rfl

/-- `Except` `pure` is `Except.ok`, definitional. Normalizes the do-elaborated
`pure`s so the `bind`/`tryCatch` `.ok` lemmas fire. -/
theorem epure {ε α} (a : α) : (pure a : Except ε α) = Except.ok a := rfl

/-- `Except` `throw` is `Except.error`, definitional. -/
theorem ethrow {ε α} (e : ε) : (throw e : Except ε α) = Except.error e := rfl

/-- **`computeDeposit` success reduction.** A `.success` outcome forces the body's
happy path: the shares priced (nonzero), the assets re-priced, and the internal
`operator_gt` guard reads `false` (`amountDeposit' ≤ amountDeposit`). The
`try`/`catch` handler can only produce `.error` codes, so it is ruled out. -/
theorem computeDeposit_success_reduces (v : Vault) (amount c s : STAmount)
    (hok : computeDeposit v amount = .ok (.success c s)) :
    ∃ shares : STAmount,
      assetsToSharesDeposit v amount = .ok shares ∧
      shares.isZero = false ∧
      sharesToAssetsDeposit v shares = .ok c ∧
      c.operator_gt amount = .ok false ∧
      s = shares := by
  unfold computeDeposit at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  -- The handler can only yield `.error` codes, so a `.success` forces the body path.
  have handler_absurd : ∀ (e : Error),
      tryCatch (Except.error e : Except Error (DoResultPR ComputeDepositResult ComputeDepositResult PUnit))
        (fun e => if isOverflow e = true then
            pure (DoResultPR.return (ComputeDepositResult.error TER.tecPATH_DRY) PUnit.unit)
          else throw e >>= fun y => pure (DoResultPR.pure y PUnit.unit)) = Except.ok rr → False := by
    intro e htc'
    rw [tryCatch_error] at htc'
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc'
      rw [← Except.ok.inj htc'] at hK; exact absurd hK (by simp [epure])
    · rw [if_neg hov, ethrow, err_bind] at htc'
      exact absurd htc' (by simp)
  cases hatsd : assetsToSharesDeposit v amount with
  | error e => rw [hatsd, err_bind] at htc; exact (handler_absurd e htc).elim
  | ok shares =>
    simp only [hatsd, ok_bind, epure] at htc
    by_cases hz : shares.isZero = true
    · rw [if_pos hz, tryCatch_ok] at htc
      rw [← Except.ok.inj htc] at hK; exact absurd hK (by simp [epure])
    · rw [if_neg hz] at htc
      cases hsad : sharesToAssetsDeposit v shares with
      | error e2 => rw [hsad, err_bind] at htc; exact (handler_absurd e2 htc).elim
      | ok amountDeposit' =>
        simp only [hsad, ok_bind] at htc
        cases hgt : amountDeposit'.operator_gt amount with
        | error e3 => rw [hgt, err_bind] at htc; exact (handler_absurd e3 htc).elim
        | ok gtb =>
          simp only [hgt, ok_bind] at htc
          by_cases hgtb : gtb = true
          · rw [if_pos hgtb, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK; exact absurd hK (by simp [epure])
          · rw [if_neg hgtb, tryCatch_ok] at htc
            have hgtf : gtb = false := by simpa using hgtb
            rw [← Except.ok.inj htc] at hK
            have hK2 : Except.ok (ComputeDepositResult.success amountDeposit' shares)
                = Except.ok (ComputeDepositResult.success c s) := hK
            obtain ⟨hc, hs⟩ := ComputeDepositResult.success.inj (Except.ok.inj hK2)
            subst hc
            refine ⟨shares, ?_, ?_, ?_, ?_, ?_⟩
            · rfl
            · simpa using hz
            · exact hsad
            · rw [← hgtf]; exact hgt
            · exact hs.symm

/-- A `false` `operator_gt` on comparable operands is a `≤` on values. Turns the
`computeDeposit` internal guard into the charge bound
`amountDeposit' ≤ amountDeposit`. -/
theorem STAmount.operator_gt_false_le (lhs rhs : STAmount) (h : STAmount.CmpFaithful lhs rhs)
    (hgt : lhs.operator_gt rhs = .ok false) : lhs.toRat ≤ rhs.toRat := by
  rw [STAmount.operator_gt_eq lhs rhs h, Except.ok.injEq, decide_eq_false_iff_not, not_lt] at hgt
  exact hgt

/-- **`computeDeposit` charge bound.** On comparable operands the internal
`operator_gt` guard means the charge never exceeds the rounded deposit:
`amountDeposit'.toRat ≤ amountDeposit.toRat`. -/
theorem computeDeposit_success_charge_le (v : Vault) (amount c s : STAmount)
    (hcmp : STAmount.CmpFaithful c amount)
    (hok : computeDeposit v amount = .ok (.success c s)) :
    c.toRat ≤ amount.toRat := by
  obtain ⟨_, _, _, _, hgt, _⟩ := computeDeposit_success_reduces v amount c s hok
  exact STAmount.operator_gt_false_le c amount hcmp hgt

/-- **Deposit guard extraction.** A deposit that runs without a throw and returns
no error code exposes: the rounded `amount` (nonzero), the passed guards, the
raw `computeDeposit` asset and the final asset stored after clamping, the three
`toNumber`/`operator_add` field updates, the passed `assetsMaximum` guard, and
the exact success record.

Source semantics: a real deposit clamps the raw `computeDeposit` asset before
checking `isFractionalNonPositive`; only that accepted, clamped asset is stored
and returned. -/
theorem Vault.deposit_success_reduces (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult) (hok : v.deposit amountDeposit isDonation = .ok r)
    (herr : r.error = none) :
    ∃ (amount rawAssetDeposited assetDeposited sharesCreated : STAmount) (cN sN at' av' st' : Number),
      roundToVaultExponent amountDeposit v.assetsTotal = .ok amount ∧
      amount.isZero = false ∧
      (isDonation = true → v.sharesTotal.mantissa_ ≠ 0) ∧
      (isDonation = false → v.isInsolvent = false) ∧
      (isDonation = true → rawAssetDeposited = amount ∧ assetDeposited = amount ∧
        sharesCreated = STAmount.zero .int64) ∧
      (isDonation = false → computeDeposit v amount =
        .ok (.success rawAssetDeposited sharesCreated) ∧
        clampToSumExponent v.assetsTotal rawAssetDeposited = .ok assetDeposited ∧
        assetDeposited.isFractionalNonPositive = .ok false) ∧
      assetDeposited.toNumber .to_nearest = .ok cN ∧
      sharesCreated.toNumber .to_nearest = .ok sN ∧
      v.assetsTotal.operator_add cN .to_nearest = .ok at' ∧
      v.assetsAvailable.operator_add cN .to_nearest = .ok av' ∧
      v.sharesTotal.operator_add sN .to_nearest = .ok st' ∧
      ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
        at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false ∧
      r.amountDeposit' = assetDeposited ∧ r.sharesIssued = sharesCreated ∧
      r.vault'.toRawVault =
        { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  unfold Vault.deposit at hok
  simp only [] at hok
  obtain ⟨amount, hround, hok⟩ := bind_ok_peel _ _ _ hok
  have hcontra : ∀ ter, DepositResult.rejected v ter = r → False := by
    intro ter h; rw [← h] at herr; simp [DepositResult.rejected] at herr
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · -- donation: assetDeposited = amount, sharesCreated = zero
          rw [if_neg (by simp [hd])] at hok
          obtain ⟨cN, hcN, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨sN, hsN, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
            at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
          · rw [if_pos hm] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
          · rw [if_neg hm] at hok
            have hsh : v.sharesTotal.mantissa_ ≠ 0 := by
              intro h0
              rw [h0] at h2; simp [hd] at h2
            obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
            obtain rfl := Except.ok.inj hok
            exact ⟨amount, amount, amount, STAmount.zero .int64, cN, sN, at', av', st',
              hround, by simpa using h1, fun _ => hsh, fun h => absurd h (by rw [hd]; decide),
              fun _ => ⟨rfl, rfl, rfl⟩, fun h => absurd h (by rw [hd]; decide),
              hcN, hsN, hat, hav, hst, by simpa using hm,
              rfl, rfl, (RawVault.to_lawful_ok htl).1⟩
        · -- real deposit: assetDeposited, sharesCreated from computeDeposit success
          rw [if_pos (by simpa using hd)] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          cases cres with
          | error e =>
            simp only [] at hok
            exact absurd (Except.ok.inj hok) (hcontra _)
          | success rawAssetDeposited s =>
            simp only [] at hok
            -- The model stores and returns only the clamped, precision-accepted asset.
            obtain ⟨assetDeposited, hclamp, hok⟩ := bind_ok_peel _ _ _ hok
            cases hprecision : assetDeposited.isFractionalNonPositive with
            | error e =>
              rw [hprecision, err_bind] at hok
              exact absurd hok (by simp)
            | ok isFractionalNonPositive =>
              simp only [hprecision, ok_bind] at hok
              by_cases hprecision' : isFractionalNonPositive = true
              · rw [if_pos hprecision'] at hok
                exact (hcontra _ (Except.ok.inj hok)).elim
              · rw [if_neg hprecision'] at hok
                have hprecisionFalse : isFractionalNonPositive = false := by
                  simpa using hprecision'
                obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨sN, hsN, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
                by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
                  at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
                · rw [if_pos hm] at hok; exact (hcontra _ (Except.ok.inj hok)).elim
                · rw [if_neg hm] at hok
                  have hins : v.isInsolvent = false := by
                    have hnd : isDonation = false := by simpa using hd
                    rw [hnd] at h3; simpa using h3
                  obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
                  obtain rfl := Except.ok.inj hok
                  exact ⟨amount, rawAssetDeposited, assetDeposited, s, n1, sN, at', av', st',
                    hround, by simpa using h1,
                    fun h => absurd h (by simp [hd]),
                    fun _ => hins,
                    fun h => absurd h (by simp [hd]),
                    fun _ => ⟨hcd, hclamp, by rw [← hprecisionFalse]; exact hprecision⟩,
                    hn1, hsN, hat, hav, hst, by simpa using hm,
                    rfl, rfl, (RawVault.to_lawful_ok htl).1⟩

end XRPL.Model.SingleAssetVault
