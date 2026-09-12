import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.NumericType

namespace XRPL.Model.Lending

open XRPL.Model.Protocol (Number NumericType Error numberExponent)

-- Any container of funds a loan broker can draw on to issue loans. `exponent` is the scale of
-- `assetsTotal`, derived by default, so an implementation only has to supply the first two.
class AssetPool (α : Type) where
  assets : α → Number
  numericType : α → NumericType

def AssetPool.exponent {α : Type} [AssetPool α] (pool : α) : Except Error Int :=
  numberExponent (AssetPool.assets pool) (AssetPool.numericType pool)

end XRPL.Model.Lending
