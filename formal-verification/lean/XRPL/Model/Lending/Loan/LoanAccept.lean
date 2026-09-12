import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- LoanAccept -> preclaim
def Loan.canAccept (loan : Loan) (ledgerCloseTime : UInt32) : TER :=
  if !loan.isPending then .tecNO_PERMISSION
  else if hasExpired ledgerCloseTime loan.schedule.startDate then .tecEXPIRED
  else .tesSUCCESS

-- LoanAccept -> doApply
def Loan.accept (loan : Loan) (vault : Vault) : Except Error (LoanResult LoanVault) := do
  let reservedAfter ← vault.assetsReserved.operator_sub loan.principalOutstanding .to_nearest
  let rawVault' : RawVault := { vault.toRawVault with assetsReserved := reservedAfter }

  let vault' ← rawVault'.to_lawful
  let loan' := { loan with isPending := false }

  return .ok { vaultIdentity := loan.vaultIdentity, loan := loan', vault := vault' }

end XRPL.Model.Lending
