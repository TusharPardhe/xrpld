import XRPL.FFI.Protocol.NumberFFI
import XRPL.Model.Lending.Amortization
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.Loan

/-! Scalar, representation-stable Lending FFI.  `Number` uses the existing
`lean_number_*` ABI; dates and tenth-bips are unsigned fixed-width values.
Identity-bearing ledger entries deliberately are not projected here. -/
namespace XRPL.FFI

open XRPL.Model.Protocol
open XRPL.Model.Lending

@[export lean_lending_has_expired]
def lending_has_expired (now expiry exclusive : UInt32) : UInt8 :=
  if hasExpired now expiry (exclusive != 0) then 1 else 0

@[export lean_lending_schedule_build]
def lending_schedule_build (interval total grace start now : UInt32) (twoStep : UInt8) : LoanSchedule :=
  LoanSchedule.build (some interval) (some total) (some grace) start now (twoStep != 0)

@[export lean_lending_schedule_interval]
def lending_schedule_interval (x : LoanSchedule) : UInt32 := x.paymentInterval
@[export lean_lending_schedule_total]
def lending_schedule_total (x : LoanSchedule) : UInt32 := x.paymentTotal
@[export lean_lending_schedule_grace]
def lending_schedule_grace (x : LoanSchedule) : UInt32 := x.gracePeriod
@[export lean_lending_schedule_start]
def lending_schedule_start (x : LoanSchedule) : UInt32 := x.startDate
@[export lean_lending_schedule_time_check]
def lending_schedule_time_check (x : LoanSchedule) : Int32 :=
  x.checkTimeAvailability.code

end XRPL.FFI
