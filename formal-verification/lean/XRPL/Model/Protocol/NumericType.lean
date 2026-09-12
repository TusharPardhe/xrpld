namespace XRPL.Model.Protocol

inductive NumericType where
  | integral (maxValue : UInt64) (maxOffset : Int) (mulSqrt : UInt64) (mulShift : UInt64)
  | fractional
  deriving DecidableEq, Repr, Hashable

def NumericType.native : NumericType := .integral 100000000000000000 17 3000000000 2095475792
def NumericType.int64 : NumericType := .integral 9223372036854775807 18 3037000499 2147483648

def NumericType.isIntegral : NumericType → Bool
  | .integral _ _ _ _ => true
  | .fractional => false

-- Bound accessors (meaningful only for `integral`, so `fractional` returns 0).
def NumericType.maxValue : NumericType → UInt64
  | .integral mv _ _ _ => mv | .fractional => 0
def NumericType.maxOffset : NumericType → Int
  | .integral _ mo _ _ => mo | .fractional => 0
def NumericType.mulSqrt : NumericType → UInt64
  | .integral _ _ ms _ => ms | .fractional => 0
def NumericType.mulShift : NumericType → UInt64
  | .integral _ _ _ msh => msh | .fractional => 0

end XRPL.Model.Protocol
