import XRPL.Model.Vault.Terminal
import XRPL.Properties.Vault.AssociateAsset

/-! # Terminal Vault transition contracts

These theorems are intentionally separate from the raw accuracy modules. Their
raw `...associateAsset_rounds` statements continue to describe the pre-
association results exactly; terminal callers instead receive the associated
SLE that C++ commits.
-/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The common five-field commit invariant supplied by one successful terminal
association. -/
theorem Vault.terminal_association_success (before after : Vault)
    (hok : before.associateAsset = .ok after) :
    ¬ STAmount.isRounded after.numericType after.assetsTotal ∧
    ¬ STAmount.isRounded after.numericType after.assetsAvailable ∧
    ¬ STAmount.isRounded after.numericType after.assetsReserved ∧
    ¬ STAmount.isRounded after.numericType after.lossUnrealized ∧
    (∀ maximum ∈ after.assetsMaximum,
      ¬ STAmount.isRounded after.numericType maximum) ∧
    after.sharesTotal = before.sharesTotal ∧ after.numericType = before.numericType ∧
      after.scale = before.scale := by
  rcases Vault.associateAsset_success_unrounded before after hok with
    ⟨hAT, hAV, hAR, hLU, hMax⟩
  rcases Vault.associateAsset_success_preserves_nonAsset before after hok with
    ⟨hShares, hType, hScale⟩
  exact ⟨hAT, hAV, hAR, hLU, hMax, hShares, hType, hScale⟩

/-- Terminal creation treats the optional maximum as an asset field instead of
asserting that a raw, unconstrained maximum was already on-grid. -/
theorem RawVault.to_lawful_terminal_success (raw : RawVault) (result : Vault)
    (hok : raw.to_lawful_terminal = .ok result) :
    ∃ pre : Vault, raw.to_lawful = .ok pre ∧
      ¬ STAmount.isRounded result.numericType result.assetsTotal ∧
      ¬ STAmount.isRounded result.numericType result.assetsAvailable ∧
      ¬ STAmount.isRounded result.numericType result.assetsReserved ∧
      ¬ STAmount.isRounded result.numericType result.lossUnrealized ∧
      (∀ maximum ∈ result.assetsMaximum,
        ¬ STAmount.isRounded result.numericType maximum) ∧
      result.sharesTotal = pre.sharesTotal ∧ result.numericType = pre.numericType ∧
        result.scale = pre.scale := by
  unfold RawVault.to_lawful_terminal at hok
  obtain ⟨pre, hpre, hok⟩ := bind_ok_peel _ _ _ hok
  exact ⟨pre, hpre, Vault.terminal_association_success pre result hok⟩

private theorem terminal_failure_atomic {α : Type} (transition : Except Error α)
    (error : Error) (herror : transition = .error error) (result : α) :
    transition ≠ .ok result := by
  rw [herror]
  simp

/-- Terminal force-burn success is one raw share mutation followed by one asset
association. The raw mutation is retained as evidence while the exposed Vault
has all five asset fields associated. -/
theorem Vault.burnShares_terminal_success (v : Vault) (sharesDestroyed : STAmount)
    (result : Vault) (hok : v.burnShares_terminal sharesDestroyed = .ok result) :
    ¬ STAmount.isRounded result.numericType result.assetsTotal ∧
    ¬ STAmount.isRounded result.numericType result.assetsAvailable ∧
    ¬ STAmount.isRounded result.numericType result.assetsReserved ∧
    ¬ STAmount.isRounded result.numericType result.lossUnrealized ∧
    (∀ maximum ∈ result.assetsMaximum,
      ¬ STAmount.isRounded result.numericType maximum) ∧
    ∃ raw, v.burnShares sharesDestroyed = .ok raw ∧
      result.sharesTotal = raw.sharesTotal ∧ result.numericType = raw.numericType ∧
        result.scale = raw.scale := by
  unfold Vault.burnShares_terminal at hok
  obtain ⟨raw, hraw, hassoc⟩ := bind_ok_peel _ _ _ hok
  have hresult : raw.associateAsset = .ok result := hassoc
  obtain ⟨hAT, hAV, hAR, hLU, hMax, hShares, hType, hScale⟩ :=
    Vault.terminal_association_success raw result hresult
  exact ⟨hAT, hAV, hAR, hLU, hMax, raw, hraw, hShares, hType, hScale⟩

/-- If the terminal association after a raw force-burn fails, the terminal
transition has no successful post-state; the raw result remains internal. -/
theorem Vault.burnShares_terminal_association_failure_atomic (v : Vault)
    (sharesDestroyed : STAmount) (raw : Vault) (error : Error)
    (hraw : v.burnShares sharesDestroyed = .ok raw)
    (hassoc : raw.associateAsset = .error error) (result : Vault) :
    v.burnShares_terminal sharesDestroyed ≠ .ok result := by
  apply terminal_failure_atomic (v.burnShares_terminal sharesDestroyed) error
  unfold Vault.burnShares_terminal
  rw [hraw]
  simp only [ok_bind]
  exact hassoc

/-- The terminal result preserves every raw deposit output other than the one
Vault field intentionally replaced by its associated final form. -/
theorem DepositResult.associateAssetTerminal_success (raw result : DepositResult)
    (hok : raw.associateAssetTerminal = .ok result) (hsuccess : result.error = none) :
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsTotal ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsReserved ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.lossUnrealized ∧
    (∀ maximum ∈ result.vault'.assetsMaximum,
      ¬ STAmount.isRounded result.vault'.numericType maximum) ∧
    result.amountDeposit' = raw.amountDeposit' ∧ result.sharesIssued = raw.sharesIssued ∧
      result.error = raw.error ∧ result.vault'.sharesTotal = raw.vault'.sharesTotal ∧
      result.vault'.numericType = raw.vault'.numericType ∧ result.vault'.scale = raw.vault'.scale := by
  unfold DepositResult.associateAssetTerminal at hok
  split at hok
  · next hraw =>
      have heq : raw = result := Except.ok.inj hok
      subst result
      cases herror : raw.error <;> simp_all
  · next hraw =>
      obtain ⟨vault, hvault, hok⟩ := bind_ok_peel _ _ _ hok
      have hresult : { raw with vault' := vault } = result := Except.ok.inj hok
      cases hresult
      rcases Vault.terminal_association_success raw.vault' vault hvault with
        ⟨hAT, hAV, hAR, hLU, hMax, hShares, hType, hScale⟩
      exact ⟨hAT, hAV, hAR, hLU, hMax, rfl, rfl, rfl, hShares, hType, hScale⟩

/-- Terminal deposit success is the raw deposit followed by exactly one
association, preserving its non-asset result values. -/
theorem Vault.deposit_terminal_success (v : Vault) (amount : STAmount) (donation : Bool)
    (result : DepositResult) (hok : v.deposit_terminal amount donation = .ok result)
    (hsuccess : result.error = none) :
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsTotal ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsReserved ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.lossUnrealized ∧
    (∀ maximum ∈ result.vault'.assetsMaximum,
      ¬ STAmount.isRounded result.vault'.numericType maximum) ∧
    ∃ raw, v.deposit amount donation = .ok raw ∧
      result.amountDeposit' = raw.amountDeposit' ∧ result.sharesIssued = raw.sharesIssued ∧
      result.error = raw.error := by
  unfold Vault.deposit_terminal at hok
  obtain ⟨raw, hraw, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨hAT, hAV, hAR, hLU, hMax, ha, hs, he, -, -, -⟩ :=
    DepositResult.associateAssetTerminal_success raw result hok hsuccess
  exact ⟨hAT, hAV, hAR, hLU, hMax, raw, hraw, ha, hs, he⟩

/-- Association failure after a raw successful deposit has no terminal success
post-state, so the raw tentative vault is never committed. -/
theorem Vault.deposit_terminal_association_failure_atomic (v : Vault) (amount : STAmount)
    (donation : Bool) (raw : DepositResult) (error : Error)
    (hraw : v.deposit amount donation = .ok raw) (hsuccess : raw.error = none)
    (hassoc : raw.vault'.associateAsset = .error error) (result : DepositResult) :
    v.deposit_terminal amount donation ≠ .ok result := by
  apply terminal_failure_atomic (v.deposit_terminal amount donation) error
  unfold Vault.deposit_terminal
  rw [hraw]
  simp only [ok_bind]
  unfold DepositResult.associateAssetTerminal
  simp [hsuccess, hassoc]

/-- The terminal result preserves every raw withdrawal output other than the
associated final Vault. -/
theorem WithdrawResult.associateAssetTerminal_success (raw result : WithdrawResult)
    (hok : raw.associateAssetTerminal = .ok result) (hsuccess : result.error = none) :
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsTotal ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsReserved ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.lossUnrealized ∧
    (∀ maximum ∈ result.vault'.assetsMaximum,
      ¬ STAmount.isRounded result.vault'.numericType maximum) ∧
    result.assets' = raw.assets' ∧ result.sharesBurned = raw.sharesBurned ∧
      result.error = raw.error ∧ result.vault'.sharesTotal = raw.vault'.sharesTotal ∧
      result.vault'.numericType = raw.vault'.numericType ∧ result.vault'.scale = raw.vault'.scale := by
  unfold WithdrawResult.associateAssetTerminal at hok
  split at hok
  · next hraw =>
      have heq : raw = result := Except.ok.inj hok
      subst result
      cases herror : raw.error <;> simp_all
  · next hraw =>
      obtain ⟨vault, hvault, hok⟩ := bind_ok_peel _ _ _ hok
      have hresult : { raw with vault' := vault } = result := Except.ok.inj hok
      cases hresult
      rcases Vault.terminal_association_success raw.vault' vault hvault with
        ⟨hAT, hAV, hAR, hLU, hMax, hShares, hType, hScale⟩
      exact ⟨hAT, hAV, hAR, hLU, hMax, rfl, rfl, rfl, hShares, hType, hScale⟩

/-- The terminal result preserves every raw clawback output other than the
associated final Vault. -/
theorem ClawbackResult.associateAssetTerminal_success (raw result : ClawbackResult)
    (hok : raw.associateAssetTerminal = .ok result) (hsuccess : result.error = none) :
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsTotal ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsReserved ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.lossUnrealized ∧
    (∀ maximum ∈ result.vault'.assetsMaximum,
      ¬ STAmount.isRounded result.vault'.numericType maximum) ∧
    result.assetsRecovered = raw.assetsRecovered ∧ result.sharesDestroyed = raw.sharesDestroyed ∧
      result.error = raw.error ∧ result.vault'.sharesTotal = raw.vault'.sharesTotal ∧
      result.vault'.numericType = raw.vault'.numericType ∧ result.vault'.scale = raw.vault'.scale := by
  unfold ClawbackResult.associateAssetTerminal at hok
  split at hok
  · next hraw =>
      have heq : raw = result := Except.ok.inj hok
      subst result
      cases herror : raw.error <;> simp_all
  · next hraw =>
      obtain ⟨vault, hvault, hok⟩ := bind_ok_peel _ _ _ hok
      have hresult : { raw with vault' := vault } = result := Except.ok.inj hok
      cases hresult
      rcases Vault.terminal_association_success raw.vault' vault hvault with
        ⟨hAT, hAV, hAR, hLU, hMax, hShares, hType, hScale⟩
      exact ⟨hAT, hAV, hAR, hLU, hMax, rfl, rfl, rfl, hShares, hType, hScale⟩

/-- Terminal withdrawal success is the raw withdrawal followed by exactly one
association, preserving its raw payout and share-burn outputs. -/
theorem Vault.withdraw_terminal_success (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (result : WithdrawResult) (hok : v.withdraw_terminal amount waive = .ok result)
    (hsuccess : result.error = none) :
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsTotal ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsReserved ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.lossUnrealized ∧
    (∀ maximum ∈ result.vault'.assetsMaximum,
      ¬ STAmount.isRounded result.vault'.numericType maximum) ∧
    ∃ raw, v.withdraw amount waive = .ok raw ∧ result.assets' = raw.assets' ∧
      result.sharesBurned = raw.sharesBurned ∧ result.error = raw.error := by
  unfold Vault.withdraw_terminal at hok
  obtain ⟨raw, hraw, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨hAT, hAV, hAR, hLU, hMax, hAssets, hShares, hError, -, -, -⟩ :=
    WithdrawResult.associateAssetTerminal_success raw result hok hsuccess
  exact ⟨hAT, hAV, hAR, hLU, hMax, raw, hraw, hAssets, hShares, hError⟩

/-- Association failure after a raw successful withdrawal exposes no terminal
success post-state. -/
theorem Vault.withdraw_terminal_association_failure_atomic (v : Vault) (amount : WithdrawAmount)
    (waive : Bool) (raw : WithdrawResult) (error : Error)
    (hraw : v.withdraw amount waive = .ok raw) (hsuccess : raw.error = none)
    (hassoc : raw.vault'.associateAsset = .error error) (result : WithdrawResult) :
    v.withdraw_terminal amount waive ≠ .ok result := by
  apply terminal_failure_atomic (v.withdraw_terminal amount waive) error
  unfold Vault.withdraw_terminal
  rw [hraw]
  simp only [ok_bind]
  unfold WithdrawResult.associateAssetTerminal
  simp [hsuccess, hassoc]

/-- Terminal clawback success is the raw clawback followed by exactly one
association, preserving its raw recovery and share-destruction outputs. -/
theorem Vault.clawback_terminal_success (v : Vault) (assets holderShares : STAmount)
    (result : ClawbackResult) (hok : v.clawback_terminal assets holderShares = .ok result)
    (hsuccess : result.error = none) :
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsTotal ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.assetsReserved ∧
    ¬ STAmount.isRounded result.vault'.numericType result.vault'.lossUnrealized ∧
    (∀ maximum ∈ result.vault'.assetsMaximum,
      ¬ STAmount.isRounded result.vault'.numericType maximum) ∧
    ∃ raw, v.clawback assets holderShares = .ok raw ∧
      result.assetsRecovered = raw.assetsRecovered ∧ result.sharesDestroyed = raw.sharesDestroyed ∧
        result.error = raw.error := by
  unfold Vault.clawback_terminal at hok
  obtain ⟨raw, hraw, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨hAT, hAV, hAR, hLU, hMax, hAssets, hShares, hError, -, -, -⟩ :=
    ClawbackResult.associateAssetTerminal_success raw result hok hsuccess
  exact ⟨hAT, hAV, hAR, hLU, hMax, raw, hraw, hAssets, hShares, hError⟩

/-- Association failure after a raw successful clawback exposes no terminal
success post-state. -/
theorem Vault.clawback_terminal_association_failure_atomic (v : Vault)
    (assets holderShares : STAmount) (raw : ClawbackResult) (error : Error)
    (hraw : v.clawback assets holderShares = .ok raw) (hsuccess : raw.error = none)
    (hassoc : raw.vault'.associateAsset = .error error) (result : ClawbackResult) :
    v.clawback_terminal assets holderShares ≠ .ok result := by
  apply terminal_failure_atomic (v.clawback_terminal assets holderShares) error
  unfold Vault.clawback_terminal
  rw [hraw]
  simp only [ok_bind]
  unfold ClawbackResult.associateAssetTerminal
  simp [hsuccess, hassoc]

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

/-- A successful terminal association of a lending state has the same five
associated Vault fields and preserves the Vault's non-asset fields. -/
theorem LendingState.associateVaultTerminal_success (raw result : LendingState)
    (hok : raw.associateVaultTerminal = .ok result) :
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsTotal ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsReserved ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.lossUnrealized ∧
    (∀ maximum ∈ result.vault.assetsMaximum,
      ¬ STAmount.isRounded result.vault.numericType maximum) ∧
    result.vault.sharesTotal = raw.vault.sharesTotal ∧
      result.vault.numericType = raw.vault.numericType ∧ result.vault.scale = raw.vault.scale := by
  unfold LendingState.associateVaultTerminal at hok
  obtain ⟨vault, hvault, hok⟩ := bind_ok_peel _ _ _ hok
  have hresult : { raw with vault } = result := Except.ok.inj hok
  cases hresult
  exact Vault.terminal_association_success raw.vault vault hvault

/-- A successful terminal association of a broker/vault state has the same
five associated Vault fields and preserves its Vault non-asset fields. -/
theorem BrokerVault.associateVaultTerminal_success (raw result : BrokerVault)
    (hok : raw.associateVaultTerminal = .ok result) :
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsTotal ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsReserved ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.lossUnrealized ∧
    (∀ maximum ∈ result.vault.assetsMaximum,
      ¬ STAmount.isRounded result.vault.numericType maximum) ∧
    result.vault.sharesTotal = raw.vault.sharesTotal ∧
      result.vault.numericType = raw.vault.numericType ∧ result.vault.scale = raw.vault.scale := by
  unfold BrokerVault.associateVaultTerminal at hok
  obtain ⟨vault, hvault, hok⟩ := bind_ok_peel _ _ _ hok
  have hresult : { raw with vault } = result := Except.ok.inj hok
  cases hresult
  exact Vault.terminal_association_success raw.vault vault hvault

/-- A successful terminal association of a loan/vault state has the same five
associated Vault fields and preserves its Vault non-asset fields. -/
theorem LoanVault.associateVaultTerminal_success (raw result : LoanVault)
    (hok : raw.associateVaultTerminal = .ok result) :
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsTotal ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsAvailable ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.assetsReserved ∧
    ¬ STAmount.isRounded result.vault.numericType result.vault.lossUnrealized ∧
    (∀ maximum ∈ result.vault.assetsMaximum,
      ¬ STAmount.isRounded result.vault.numericType maximum) ∧
    result.vault.sharesTotal = raw.vault.sharesTotal ∧
      result.vault.numericType = raw.vault.numericType ∧ result.vault.scale = raw.vault.scale := by
  unfold LoanVault.associateVaultTerminal at hok
  obtain ⟨vault, hvault, hok⟩ := bind_ok_peel _ _ _ hok
  have hresult : { raw with vault } = result := Except.ok.inj hok
  cases hresult
  exact Vault.terminal_association_success raw.vault vault hvault

/-- `LoanResult.associateTerminal` is atomic: rejection remains unchanged, and
success is present exactly when the supplied terminal association succeeds. -/
theorem LoanResult.associateTerminal_success {α : Type} (associate : α → Except Error α)
    (raw result : LoanResult α) (hok : raw.associateTerminal associate = .ok result) :
    (∃ ter, raw = .rejected ter ∧ result = .rejected ter) ∨
      ∃ before after, raw = .ok before ∧ associate before = .ok after ∧ result = .ok after := by
  cases raw with
  | rejected ter =>
      left
      exact ⟨ter, rfl, by simpa [LoanResult.associateTerminal] using hok.symm⟩
  | ok before =>
      right
      unfold LoanResult.associateTerminal at hok
      obtain ⟨after, hassociate, hresult⟩ := bind_ok_peel _ _ _ hok
      exact ⟨before, after, rfl, hassociate, Except.ok.inj hresult.symm⟩

end XRPL.Model.Lending
