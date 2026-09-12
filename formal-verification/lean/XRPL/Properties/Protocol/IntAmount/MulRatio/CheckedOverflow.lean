import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount

/-! # Checked `IntAmount.mulRatio` boundary contract -/

namespace XRPL.Model.Protocol

private def minAmount : IntAmount := IntAmount.ofInt64 Int64.minValue
private def maxAmount : IntAmount := IntAmount.ofInt64 Int64.maxValue

private def exactResult : Except Error IntAmount → Except Error IntAmount → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

example : exactResult (IntAmount.mulRatio minAmount 1 1 false) (.ok minAmount) = true := by
  decide
example : exactResult (IntAmount.mulRatio minAmount 2 1 false) (.error .overflow) = true := by
  decide
example : exactResult (IntAmount.mulRatio maxAmount 2 1 false) (.error .overflow) = true := by
  decide
example : exactResult (IntAmount.mulRatio (IntAmount.ofInt64 (-10)) 3 4 false)
    (.ok (IntAmount.ofInt64 (-8))) = true := by
  decide
example : exactResult (IntAmount.mulRatio IntAmount.zero 1 0 false) (.error .divByZero) = true := by
  decide

end XRPL.Model.Protocol
