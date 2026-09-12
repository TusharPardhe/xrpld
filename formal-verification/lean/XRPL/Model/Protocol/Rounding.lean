import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount

namespace XRPL.Model.Protocol

def adjustImpreciseNumber (nt : NumericType) (value adjustment : Number) (scale : Int)
    : Except Error Number := do
  let adjusted ← value.operator_add adjustment .to_nearest
  let rounded ← STAmount.roundToNumericType nt adjusted .to_nearest (some scale)
  if rounded.signum < 0 then return Number.zero else return rounded

-- exactly representable at scale (round-down == round-up)
def isRounded (nt : NumericType) (value : Number) (scale : Int) : Except Error Bool := do
  let down ← STAmount.roundToNumericType nt value .downward (some scale)
  let up ← STAmount.roundToNumericType nt value .upward (some scale)
  return down.operator_eq up

-- Round a value at the scale, then clamp it into [0, cap].
def roundAndClamp (value cap : Number) (mode : rounding_mode) (nt : NumericType) (scale : Int)
    : Except Error Number := do
  let rounded ← STAmount.roundToNumericType nt value mode (some scale)
  return Number.clamp rounded Number.zero cap

private def sumAndRoundToExponent (amount : Number) (amountDelta : STAmount)
    (exponent : Int) (rounding : rounding_mode) : Except Error Number := do
  let numericType := amountDelta.numericType
  let amountDelta ← amountDelta.toNumber rounding
  let sum ← amount.operator_add amountDelta rounding
  let sum ← STAmount.ofNumber numericType sum rounding
  let sum ← STAmount.roundToExponent sum exponent rounding
  sum.toNumber rounding

def clampToSumExponent (amount : Number) (amountDelta : STAmount)
    : Except Error STAmount := do
  let amountDeltaAbs := if amountDelta.negative then amountDelta.operator_neg else amountDelta
  if amountDelta.integral then
    return amountDeltaAbs

  let postExponent ← postSumExponent amount amountDelta
  if amountDelta.negative then
    STAmount.roundToExponent amountDeltaAbs postExponent .downward
  else
    let sum ← sumAndRoundToExponent amount amountDeltaAbs postExponent .downward
    let amountDeltaAbs ← sum.operator_sub amount .to_nearest
    STAmount.ofNumber amountDelta.numericType amountDeltaAbs .to_nearest

end XRPL.Model.Protocol
