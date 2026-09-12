import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanDelete
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Vault.Terminal

/-! Complete identity-preserving Lending transition ABI.

These definitions take and return the model's ledger records directly.  The
versioned byte encoding is owned by `XRPL.FFI.Lending.Wire`; no model endpoint
invents an account, object, issue, credential, configuration, or transaction value.  Raw names expose the
pre-commit kernel.  Terminal names run precisely the corresponding model
terminal form, whose success branch associates the Vault exactly once.
-/
namespace XRPL.FFI

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault

def lending_raw_create := Loan.create
def lending_raw_create_pending := Loan.createPending
def lending_raw_create_immediate := Loan.createImmediate
def lending_raw_accept := Loan.accept
def lending_raw_delete := Loan.delete
def lending_raw_regular_payment := Loan.regularPayment
def lending_raw_late_payment := Loan.latePayment
def lending_raw_full_payment := Loan.fullPayment
def lending_raw_manage_impair := Loan.manageImpair
def lending_raw_manage_unimpair := Loan.manageUnimpair
def lending_raw_manage_default := Loan.manageDefault
def lending_raw_broker_create := LoanBroker.create
def lending_raw_broker_update := LoanBroker.update
def lending_raw_cover_validate := canApplyToBrokerCover
def lending_raw_cover_deposit := LoanBroker.coverDeposit
def lending_raw_cover_withdraw := LoanBroker.coverWithdraw

def lending_terminal_create := Loan.create_terminal
def lending_terminal_create_pending := Loan.createPending_terminal
def lending_terminal_create_immediate := Loan.createImmediate_terminal
def lending_terminal_accept := Loan.accept_terminal
def lending_terminal_delete := Loan.delete_terminal
def lending_terminal_regular_payment := Loan.regularPayment_terminal
def lending_terminal_late_payment := Loan.latePayment_terminal
def lending_terminal_full_payment := Loan.fullPayment_terminal
def lending_terminal_manage_impair := Loan.manageImpair_terminal
def lending_terminal_manage_unimpair := Loan.manageUnimpair_terminal
def lending_terminal_manage_default := Loan.manageDefault_terminal

end XRPL.FFI
