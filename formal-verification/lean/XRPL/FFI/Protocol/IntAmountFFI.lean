import XRPL.FFI.CommonFFI
import XRPL.Model.Protocol.IntAmount


namespace XRPL.FFI

open XRPL.Model.Protocol (IntAmount Number rounding_mode Error)

@[export lean_int_amount_of_int64]
def lean_int_amount_of_int64 (v : Int64) : Int64 :=
  (IntAmount.ofInt64 v).value

@[export lean_int_amount_of_number]
def lean_int_amount_of_number (n : Number) (mode : rounding_mode) : Except Error Int64 :=
  (IntAmount.ofNumber n mode).map (·.value)

@[export lean_int_amount_to_number]
def lean_int_amount_to_number (v : Int64) (mode : rounding_mode) : Except Error Number :=
  (IntAmount.ofInt64 v).toNumber mode

@[export lean_int_amount_eq]
def lean_int_amount_eq (v1 v2 : Int64) : UInt8 :=
  if IntAmount.operator_eq (IntAmount.ofInt64 v1) (IntAmount.ofInt64 v2) then 1 else 0

@[export lean_int_amount_ne]
def lean_int_amount_ne (v1 v2 : Int64) : UInt8 :=
  if IntAmount.operator_ne (IntAmount.ofInt64 v1) (IntAmount.ofInt64 v2) then 1 else 0

@[export lean_int_amount_eq_int]
def lean_int_amount_eq_int (v : Int64) (n : Int64) : UInt8 :=
  if IntAmount.operator_eq_int (IntAmount.ofInt64 v) n then 1 else 0

@[export lean_int_amount_ne_int]
def lean_int_amount_ne_int (v : Int64) (n : Int64) : UInt8 :=
  if IntAmount.operator_ne_int (IntAmount.ofInt64 v) n then 1 else 0

@[export lean_int_amount_lt]
def lean_int_amount_lt (v1 v2 : Int64) : UInt8 :=
  if IntAmount.operator_lt (IntAmount.ofInt64 v1) (IntAmount.ofInt64 v2) then 1 else 0

@[export lean_int_amount_le]
def lean_int_amount_le (v1 v2 : Int64) : UInt8 :=
  if IntAmount.operator_le (IntAmount.ofInt64 v1) (IntAmount.ofInt64 v2) then 1 else 0

@[export lean_int_amount_gt]
def lean_int_amount_gt (v1 v2 : Int64) : UInt8 :=
  if IntAmount.operator_gt (IntAmount.ofInt64 v1) (IntAmount.ofInt64 v2) then 1 else 0

@[export lean_int_amount_ge]
def lean_int_amount_ge (v1 v2 : Int64) : UInt8 :=
  if IntAmount.operator_ge (IntAmount.ofInt64 v1) (IntAmount.ofInt64 v2) then 1 else 0

@[export lean_int_amount_add]
def lean_int_amount_add (v1 v2 : Int64) : Int64 :=
  ((IntAmount.ofInt64 v1).operator_add (IntAmount.ofInt64 v2)).value

@[export lean_int_amount_sub]
def lean_int_amount_sub (v1 v2 : Int64) : Int64 :=
  ((IntAmount.ofInt64 v1).operator_sub (IntAmount.ofInt64 v2)).value

@[export lean_int_amount_neg]
def lean_int_amount_neg (v : Int64) : Int64 :=
  (IntAmount.ofInt64 v).operator_neg.value

@[export lean_int_amount_mul]
def lean_int_amount_mul (v : Int64) (rhs : Int64) : Int64 :=
  ((IntAmount.ofInt64 v).operator_mul rhs).value

@[export lean_int_amount_add_int]
def lean_int_amount_add_int (v : Int64) (n : Int64) : Int64 :=
  ((IntAmount.ofInt64 v).operator_add_int n).value

@[export lean_int_amount_sub_int]
def lean_int_amount_sub_int (v : Int64) (n : Int64) : Int64 :=
  ((IntAmount.ofInt64 v).operator_sub_int n).value

@[export lean_int_amount_mul_ratio]
def lean_int_amount_mul_ratio (v : Int64) (num den : UInt32) (roundUp : UInt8)
    : Except Error Int64 :=
  (IntAmount.mulRatio (IntAmount.ofInt64 v) num den (roundUp != 0)).map (·.value)

end XRPL.FFI
