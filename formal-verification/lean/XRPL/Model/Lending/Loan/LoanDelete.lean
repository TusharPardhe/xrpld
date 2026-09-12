import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- LoanDelete -> preclaim
def Loan.canDelete (loan : Loan) : TER :=
  if !loan.isPending && loan.paymentRemaining > 0 then .tecHAS_OBLIGATIONS
  else .tesSUCCESS

-- bug: C++ hardcodes the accrual formula here, which is wrong for cash-basis vaults
def Loan.deletePending (loan : Loan) (vault : Vault) (broker : LoanBroker) : Except Error (LoanResult BrokerVault) := do
  let vaultExponent ← numberExponent vault.assetsTotal vault.numericType
  let availableAfter ← vault.assetsAvailable.operator_add loan.principalOutstanding .to_nearest
  let reservedAfter ← vault.assetsReserved.operator_sub loan.principalOutstanding .to_nearest

  let rawVault' : RawVault := { vault.toRawVault with assetsAvailable := availableAfter, assetsReserved := reservedAfter }
  let vault' ← rawVault'.to_lawful

  let debtAfter ← adjustImpreciseNumber vault.numericType broker.debtTotal
    loan.principalOutstanding.operator_neg vaultExponent
  let broker' := { broker with debtTotal := debtAfter, loanCount := broker.loanCount - 1 }

  return .ok { vaultIdentity := loan.vaultIdentity, vault := vault', broker := broker' }

def Loan.deleteActive (loan : Loan) (vault : Vault) (broker : LoanBroker) : LoanResult BrokerVault :=
  let loanCount := broker.loanCount - 1
  let newDebt := if loanCount == 0 then Number.zero else broker.debtTotal

  let broker' := { broker with loanCount := loanCount, debtTotal := newDebt }
  .ok { vaultIdentity := loan.vaultIdentity, vault := vault, broker := broker' }

-- LoanDelete -> doApply
def Loan.delete (loan : Loan) (vault : Vault) (broker : LoanBroker) : Except Error (LoanResult BrokerVault) :=
  if loan.isPending then loan.deletePending vault broker
  else .ok (Loan.deleteActive loan vault broker)

end XRPL.Model.Lending
