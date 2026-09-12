import XRPL.Properties.Vault.Common.DepositExits
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback

/-! # Rejected operations leave the vault unchanged (proofs)

Each proof walks the operation's do-block and shows every exit either returns
the full rejection record (`vault' = v`, both amount fields zero) or returns
`error = none`. The `error`-carrying disjunct is then discharged by the
`isSome` hypothesis. The `*_error_unchanged_proof` corollaries keep the
vault-only conclusion. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit returning a `TER` leaves the vault unchanged and reports zero
amounts. -/
theorem Vault.deposit_error_rejected_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.amountDeposit' = STAmount.zero v.numericType ∧
    r.sharesIssued = STAmount.zero .int64 := by
  have key : (r.vault' = v ∧ r.amountDeposit' = STAmount.zero v.numericType ∧
      r.sharesIssued = STAmount.zero .int64) ∨ r.error = none := by
    unfold Vault.deposit at hok
    simp only [] at hok
    obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h1 : amount.isZero = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
    · rw [if_neg h1] at hok
      by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
      · rw [if_neg h2] at hok
        by_cases h3 : (v.isInsolvent && !isDonation) = true
        · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
        · rw [if_neg h3] at hok
          simp only [pure_bind] at hok
          by_cases hd : isDonation = true
          · rw [if_neg (by simp [hd])] at hok
            obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
            · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            · rw [if_neg hm] at hok
              obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
              injection hok with h; rw [← h]; exact .inr rfl
          · rw [if_pos (by simpa using hd)] at hok
            obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
            cases cres with
            | error e =>
              injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            | success a s =>
              simp only [] at hok
              obtain ⟨assetDeposited, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨hprecision, _, hok⟩ := bind_ok_peel _ _ _ hok
              by_cases hp : hprecision = true
              · rw [if_pos hp] at hok
                injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
              · rw [if_neg hp] at hok
                obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
                by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
                · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
                · rw [if_neg hm] at hok
                  obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
                  injection hok with h; rw [← h]; exact .inr rfl
  rcases key with h | h
  · exact h
  · rw [h] at herr; simp at herr

/-- A deposit returning a `TER` leaves the vault unchanged. -/
theorem Vault.deposit_error_unchanged_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult) (hok : v.deposit amountDeposit isDonation = .ok r)
    (herr : r.error.isSome = true) : r.vault' = v :=
  (Vault.deposit_error_rejected_proof v amountDeposit isDonation r hok herr).1

/-- A withdrawal returning a `TER` leaves the vault unchanged and reports zero
amounts. -/
theorem Vault.withdraw_error_rejected_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.assets' = STAmount.zero v.numericType ∧
    r.sharesBurned = STAmount.zero .int64 := by
  have key : (r.vault' = v ∧ r.assets' = STAmount.zero v.numericType ∧
      r.sharesBurned = STAmount.zero .int64) ∨ r.error = none := by
    unfold Vault.withdraw at hok
    simp only [] at hok
    cases amount
    all_goals {
      simp only [] at hok
      obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h1 : result.error.isSome = true
      · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
      · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
        obtain ⟨assetsNumber', _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h2 : v.assetsAvailable.operator_lt assetsNumber' = true
        · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
        · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
          obtain ⟨sta, _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases h3 : result.sharesRedeemed.operator_eq sta = true
          · rw [if_pos h3] at hok
            by_cases h4 : v.lossUnrealized.operator_ne Number.zero = true
            · rw [if_pos h4] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
              obtain ⟨allAvail, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
              injection hok with h; rw [← h]; exact .inr rfl
          · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
            obtain ⟨sbn, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨hprecision, _, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hp : hprecision = true
            · rw [if_pos hp] at hok
              injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            · rw [if_neg hp] at hok
              obtain ⟨assetsNumber'', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨sharesBurnedNumber, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨assetsTotal', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
              by_cases h5 : (assetsNumber''.mantissa_ != 0 && atr.operator_eq atr') = true
              · rw [if_pos h5] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
              · rw [if_neg h5] at hok; try simp only [pure_bind] at hok
                obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
                injection hok with h; rw [← h]; exact .inr rfl
    }
  rcases key with h | h
  · exact h
  · rw [h] at herr; simp at herr

/-- A withdrawal returning a `TER` leaves the vault unchanged. -/
theorem Vault.withdraw_error_unchanged_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    (herr : r.error.isSome = true) : r.vault' = v :=
  (Vault.withdraw_error_rejected_proof v amount waiveUnrealizedLoss r hok herr).1

/-- A clawback returning a `TER` leaves the vault unchanged and reports zero
amounts. -/
theorem Vault.clawback_error_rejected_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : v.clawback assets holderShares = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.assetsRecovered = STAmount.zero v.numericType ∧
    r.sharesDestroyed = STAmount.zero .int64 := by
  have key : (r.vault' = v ∧ r.assetsRecovered = STAmount.zero v.numericType ∧
      r.sharesDestroyed = STAmount.zero .int64) ∨ r.error = none := by
    unfold Vault.clawback at hok
    simp only [] at hok
    obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h1 : result.error.isSome = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
    · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
      by_cases h2 : result.sharesDestroyed.isZero = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
      · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
        obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨arn, _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h3 : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
        · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
        · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
          obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
          injection hok with h; rw [← h]
          cases hre : result.error with
          | none => exact .inr rfl
          | some x => rw [hre] at h1; simp at h1
  rcases key with h | h
  · exact h
  · rw [h] at herr; simp at herr

/-- A clawback returning a `TER` leaves the vault unchanged. -/
theorem Vault.clawback_error_unchanged_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : v.clawback assets holderShares = .ok r)
    (herr : r.error.isSome = true) : r.vault' = v :=
  (Vault.clawback_error_rejected_proof v assets holderShares r hok herr).1

end XRPL.Model.SingleAssetVault
