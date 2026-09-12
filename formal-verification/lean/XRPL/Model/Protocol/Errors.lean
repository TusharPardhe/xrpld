namespace XRPL.Model.Protocol

/-- Error conditions surfaced by the model's fallible arithmetic and amount operations.
Replaces the former `String` error payload. -/
inductive Error where
  | overflow
  | divByZero
  | outOfRange
  | normalize1
  | normalize1_5
  | normalize2
  | notComparable
  | cannotConvert
  | notLawful
deriving DecidableEq, Repr, Inhabited

end XRPL.Model.Protocol
