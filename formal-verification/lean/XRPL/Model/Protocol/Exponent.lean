import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount

namespace XRPL.Model.Protocol

-- exponent of a Number represented as an STAmount. Models the function `scale` from xrpld
def numberExponent (amount : Number) (nt : NumericType) : Except Error Int := do
  let a ← STAmount.ofNumber nt amount .to_nearest
  return a.exponent

def postSumExponent (amount : Number) (amountDelta : STAmount)
    : Except Error Int := do
  let numericType := amountDelta.numericType
  let amountDelta ← amountDelta.toNumber .to_nearest
  let sum ← amount.operator_add amountDelta .to_nearest
  numberExponent sum numericType

end XRPL.Model.Protocol
