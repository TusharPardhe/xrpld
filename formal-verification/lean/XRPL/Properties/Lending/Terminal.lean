import XRPL.Model.Vault.Terminal

/-! Kernel-checked contracts for the Lending terminal adapter.  These prove the
raw/terminal boundary without assuming a successful association or using an
executable decision procedure. -/
namespace XRPL.Model.Lending.TerminalProperties

open XRPL.Model.Protocol

@[simp] theorem LoanResult.associateTerminal_rejected {α : Type} (associate : α → Except Error α)
    (ter : TER) : LoanResult.associateTerminal associate (.rejected ter) = .ok (.rejected ter) := rfl

@[simp] theorem LoanResult.associateTerminal_ok {α : Type} (associate : α → Except Error α)
    (state : α) : LoanResult.associateTerminal associate (.ok state) =
      match associate state with
      | .ok associated => .ok (.ok associated)
      | .error error => .error error := by
  unfold LoanResult.associateTerminal
  cases h : associate state <;> simp [h]

theorem LoanResult.associateTerminal_success {α : Type} (associate : α → Except Error α)
    (state associated : α) (h : associate state = .ok associated) :
    LoanResult.associateTerminal associate (.ok state) = .ok (.ok associated) := by
  simp [LoanResult.associateTerminal, h]

theorem LoanResult.associateTerminal_failure_atomic {α : Type} (associate : α → Except Error α)
    (state : α) (error : Error) (h : associate state = .error error) (result : LoanResult α) :
    LoanResult.associateTerminal associate (.ok state) ≠ .ok result := by
  simp [LoanResult.associateTerminal, h]

theorem LendingState.associateVaultTerminal_success (state associated : LendingState)
    (h : state.vault.associateAsset = .ok associated.vault)
    (preserve : associated = { state with vault := associated.vault }) :
    state.associateVaultTerminal = .ok associated := by
  rw [preserve]
  simp [LendingState.associateVaultTerminal, h]

end XRPL.Model.Lending.TerminalProperties
