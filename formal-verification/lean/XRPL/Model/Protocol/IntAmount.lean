import XRPL.Model.Protocol.Number


namespace XRPL.Model.Protocol

-- Integer-valued amount (an int64 at offset 0). XRP and MPT share this one representation.
structure IntAmount where
  value : Int64
  deriving DecidableEq, Repr

def IntAmount.zero : IntAmount := { value := 0 }
def IntAmount.minPositiveAmount : IntAmount := { value := 1 }

def IntAmount.toRat (x : IntAmount) : ℚ := (x.value.toInt : ℚ)
def IntAmount.toBool (x : IntAmount) : Bool := x.value != 0
def IntAmount.signum (x : IntAmount) : Int :=
  if x.value < 0 then -1 else if x.value > 0 then 1 else 0

def IntAmount.ofInt64 (v : Int64) : IntAmount := { value := v }

def IntAmount.ofNumber (n : Number) (mode : rounding_mode) : Except Error IntAmount :=
  match n.to_rep mode with
  | .ok r => .ok { value := r }
  | .error e => .error e

def IntAmount.toNumber (x : IntAmount) (mode : rounding_mode) : Except Error Number :=
  Number.from_rep x.value 0 largeRange.min largeRange.max mode

def IntAmount.operator_eq (x y : IntAmount) : Bool := x.value == y.value
def IntAmount.operator_ne (x y : IntAmount) : Bool := x.value != y.value
def IntAmount.operator_eq_int (x : IntAmount) (v : Int64) : Bool := x.value == v
def IntAmount.operator_ne_int (x : IntAmount) (v : Int64) : Bool := x.value != v
def IntAmount.operator_lt (x y : IntAmount) : Bool := x.value < y.value
def IntAmount.operator_le (x y : IntAmount) : Bool := x.value ≤ y.value
def IntAmount.operator_gt (x y : IntAmount) : Bool := x.value > y.value
def IntAmount.operator_ge (x y : IntAmount) : Bool := x.value ≥ y.value

def IntAmount.operator_add (x y : IntAmount) : IntAmount :=
  { value := x.value + y.value }

def IntAmount.operator_sub (x y : IntAmount) : IntAmount :=
  { value := x.value - y.value }

def IntAmount.operator_neg (x : IntAmount) : IntAmount :=
  { value := -x.value }

def IntAmount.operator_mul (x : IntAmount) (rhs : Int64) : IntAmount :=
  { value := x.value * rhs }

def IntAmount.operator_add_int (x : IntAmount) (v : Int64) : IntAmount :=
  { value := x.value + v }

def IntAmount.operator_sub_int (x : IntAmount) (v : Int64) : IntAmount :=
  { value := x.value - v }

def IntAmount.mulRatio (amt : IntAmount) (num den : UInt32) (roundUp : Bool)
    : Except Error IntAmount :=
  if den == 0 then .error .divByZero
  else
    let neg := amt.value < 0
    let d : Int := (den.toNat : Int)
    let m : Int := amt.value.toInt * (num.toNat : Int)
    let q : Int := Int.tdiv m d
    let r : Int :=
      if Int.tmod m d ≠ 0 then
        if !neg && roundUp then q + 1
        else if neg && !roundUp then q - 1
        else q
      else q
    let int64Max : Int := Int64.maxValue.toInt
    let int64Min : Int := Int64.minValue.toInt
    if r > int64Max then .error .overflow
    -- rippled leaves negative int128-to-int64 out-of-range conversion implementation-defined;
    -- this model therefore uses the deterministic checked conversion contract.
    else if r < int64Min then .error .overflow
    else .ok { value := r.toInt64 }

end XRPL.Model.Protocol
