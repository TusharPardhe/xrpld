import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.LoanBroker.LoanBroker
import XRPL.Model.Lending.Identity

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

structure BrokerVault where
  vaultIdentity : VaultIdentity
  vault : Vault
  broker : LoanBroker

structure LoanVault where
  vaultIdentity : VaultIdentity
  loan : Loan
  vault : Vault

structure LendingState where
  vaultIdentity : VaultIdentity
  vault : Vault
  broker : LoanBroker
  loan : Loan

-- The result of a lending operation (the new ledger state, or the TER that rejected it)
inductive LoanResult (α : Type) where
  | ok (state : α)
  | rejected (ter : TER)

end XRPL.Model.Lending
