import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER

open XRPL.Model.Protocol (STAmount TER)

namespace XRPL.Model.Result

inductive RoundingResult where
  | rounded (amount : STAmount)
  | rejected (ter : TER)
  deriving DecidableEq

end XRPL.Model.Result
