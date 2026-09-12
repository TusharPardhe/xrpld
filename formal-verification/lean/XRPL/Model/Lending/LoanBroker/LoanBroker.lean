import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.Identity

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

structure LoanBroker where
  identity : BrokerIdentity
  managementFeeRate : TenthBips16
  coverRateMinimum : TenthBips32
  coverRateLiquidation : TenthBips32
  -- amounts in the vault's asset
  debtTotal : Number
  debtMaximum : Number
  coverAvailable : Number
  loanCount : UInt32

/-- Debt cap `2^63 − 1` as a `Number` (C++ `kMaxMpTokenAmount`). -/
def debtMaxCap : Number := Number.ofInt64 (9223372036854775807 : Int64)

/-- Max management fee rate, in tenth-bips, so 10% (C++ `kMaxManagementFeeRate`). -/
def maxManagementFeeRate : ℕ := 10_000

/-- Max cover rate, in tenth-bips, so 100% (C++ `kMaxCoverRate`). -/
def maxCoverRate : ℕ := 100_000

-- XLS-66 (32): management fee on the interest, rounded down
def computeManagementFee (nt : NumericType) (value : Number) (feeRate : TenthBips16) (exponent : Int)
    : Except Error Number := do
  let raw ← tenthBipsOfValue value feeRate.toTenthBips32 .to_nearest
  STAmount.roundToNumericType nt raw .downward (some exponent)

end XRPL.Model.Lending
