import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

namespace CashBasis

-- Apply a cash-basis payment to the vault and broker
def applyPayment (vaultIdentity : VaultIdentity) (vault : Vault) (broker : LoanBroker) (principalPaid interestPaid feePaid : Number)
    : Except Error BrokerVault := do
  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  let cash ← principalPaid.operator_add interestPaid .to_nearest
  let cashRounded ← STAmount.roundToNumericType vault.numericType cash .downward (some vaultScale)

  -- interest raises AssetsTotal, principal repays DebtTotal
  let assetsAvailable ← vault.assetsAvailable.operator_add cashRounded .to_nearest
  let assetsTotal ← vault.assetsTotal.operator_add interestPaid .to_nearest
  let debtTotal ← adjustImpreciseNumber vault.numericType broker.debtTotal principalPaid.operator_neg vaultScale

  -- if cover already meets its minimum, pay the owner, else add the fee to cover
  let minCover ← minimumBrokerCover vault.numericType broker.debtTotal broker.coverRateMinimum vaultScale
  let sendFeeToOwner := minCover.operator_le broker.coverAvailable
  let coverAvailable' ← if sendFeeToOwner then pure broker.coverAvailable
                        else broker.coverAvailable.operator_add feePaid .to_nearest

  let assetsAvailable' ← STAmount.roundToNumericType vault.numericType assetsAvailable .to_nearest none
  let assetsTotal' ← STAmount.roundToNumericType vault.numericType assetsTotal .to_nearest none
  let debtTotal' ← STAmount.roundToNumericType vault.numericType debtTotal .to_nearest none

  let rawVault' : RawVault := { vault.toRawVault with assetsTotal := assetsTotal', assetsAvailable := assetsAvailable' }
  let vault' ← rawVault'.to_lawful
  let broker' := { broker with debtTotal := debtTotal', coverAvailable := coverAvailable' }

  return { vaultIdentity := vaultIdentity, vault := vault', broker := broker' }

end CashBasis

end XRPL.Model.Lending
