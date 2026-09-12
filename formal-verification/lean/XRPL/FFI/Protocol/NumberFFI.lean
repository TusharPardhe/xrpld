import XRPL.FFI.CommonFFI
import XRPL.Model.Protocol.Number


namespace XRPL.FFI

open XRPL.Model.Protocol (Number largeRange rounding_mode Error)

@[export lean_number_build]
def lean_number_build (negative : UInt8) (mantissa : UInt64) (exponent : Int64) : Number :=
  Number.unchecked (negative != 0) mantissa exponent.toInt

@[export lean_number_build_norm]
def lean_number_build_norm (negative : UInt8) (mantissa : UInt64) (exponent : Int64) : Number :=
  (Number.normalized (negative != 0) mantissa exponent.toInt
    largeRange.min largeRange.max .to_nearest).toOption.getD Number.zero

@[export lean_number_negative]
def lean_number_negative (n : Number) : UInt8 := if n.negative_ then 1 else 0

@[export lean_number_mantissa]
def lean_number_mantissa (n : Number) : UInt64 := n.mantissa_

@[export lean_number_exponent]
def lean_number_exponent (n : Number) : Int64 := n.exponent_.toInt64

/-- Public arithmetic uses the rippled/Quaxar error contract: the model retains
normalization-stage detail for proofs, while the exported result presents each stage
failure as the public overflow category. -/
def number_arithmetic_error (error : Error) : Error :=
  match error with
  | .normalize1 | .normalize1_5 | .normalize2 => .overflow
  | error => error

/-- Apply the public arithmetic error contract without changing successful values. -/
def number_arithmetic_result (result : Except Error Number) : Except Error Number :=
  match result with
  | .ok value => .ok value
  | .error error => .error (number_arithmetic_error error)

/-! Focused regression evidence for the public Number arithmetic error contract. -/
example : number_arithmetic_error .normalize1 = .overflow := rfl
example : number_arithmetic_error .normalize1_5 = .overflow := rfl
example : number_arithmetic_error .normalize2 = .overflow := rfl
example : number_arithmetic_error .overflow = .overflow := rfl
example : number_arithmetic_error .divByZero = .divByZero := rfl
example : number_arithmetic_error .outOfRange = .outOfRange := rfl
example : number_arithmetic_error .notComparable = .notComparable := rfl
example : number_arithmetic_error .cannotConvert = .cannotConvert := rfl
example : number_arithmetic_error .notLawful = .notLawful := rfl

@[export lean_number_mul]
def lean_number_mul (a b : Number) (mode : rounding_mode) : Except Error Number :=
  number_arithmetic_result (Number.operator_mul a b mode)

@[export lean_number_div]
def lean_number_div (a b : Number) (mode : rounding_mode) : Except Error Number :=
  number_arithmetic_result (Number.operator_div a b mode)

@[export lean_number_add]
def lean_number_add (a b : Number) (mode : rounding_mode) : Except Error Number :=
  number_arithmetic_result (Number.operator_add a b mode)

@[export lean_number_sub]
def lean_number_sub (a b : Number) (mode : rounding_mode) : Except Error Number :=
  number_arithmetic_result (Number.operator_sub a b mode)

@[export lean_number_neg]
def lean_number_neg (n : Number) : Number :=
  n.operator_neg

@[export lean_number_normalize]
def lean_number_normalize (n : Number) (mode : rounding_mode) : Except Error Number :=
  n.normalize largeRange.min largeRange.max mode

@[export lean_number_signum]
def lean_number_signum (n : Number) : Int64 :=
  n.signum.toInt64

@[export lean_number_to_rep]
def lean_number_to_rep (n : Number) (mode : rounding_mode) : Except Error Int64 :=
  n.to_rep mode

@[export lean_number_eq]
def lean_number_eq (a b : Number) : UInt8 :=
  if Number.operator_eq a b then 1 else 0

@[export lean_number_ne]
def lean_number_ne (a b : Number) : UInt8 :=
  if Number.operator_ne a b then 1 else 0

@[export lean_number_lt]
def lean_number_lt (a b : Number) : UInt8 :=
  if Number.operator_lt a b then 1 else 0

@[export lean_number_le]
def lean_number_le (a b : Number) : UInt8 :=
  if Number.operator_le a b then 1 else 0

@[export lean_number_gt]
def lean_number_gt (a b : Number) : UInt8 :=
  if Number.operator_gt a b then 1 else 0

@[export lean_number_ge]
def lean_number_ge (a b : Number) : UInt8 :=
  if Number.operator_ge a b then 1 else 0

end XRPL.FFI
