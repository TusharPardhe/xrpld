import XRPL.FFI.CommonFFI
import XRPL.Model.Protocol.IOUAmount


namespace XRPL.FFI

open XRPL.Model.Protocol (IOUAmount Number rounding_mode Error)

@[export lean_iou_amount_build]
def lean_iou_amount_build (mantissa exponent : Int64) : IOUAmount :=
  { mantissa_ := mantissa, exponent_ := exponent.toInt }
@[export lean_iou_amount_mantissa]
def lean_iou_amount_mantissa (a : IOUAmount) : Int64 := a.mantissa
@[export lean_iou_amount_exponent]
def lean_iou_amount_exponent (a : IOUAmount) : Int64 := a.exponent.toInt64

@[export lean_iou_from_number]
def lean_iou_from_number (n : Number) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.fromNumber n mode

@[export lean_iou_of_mantissa_exp]
def lean_iou_of_mantissa_exp (m : Int64) (e : Int64) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.ofMantissaExp m e.toInt mode

@[export lean_iou_of_number]
def lean_iou_of_number (n : Number) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.ofNumber n mode

@[export lean_iou_to_number]
def lean_iou_to_number (a : IOUAmount) (mode : rounding_mode) : Except Error Number :=
  a.toNumber mode

@[export lean_iou_eq]
def lean_iou_eq (a b : IOUAmount) : UInt8 :=
  if IOUAmount.operator_eq a b then 1 else 0

@[export lean_iou_ne]
def lean_iou_ne (a b : IOUAmount) : UInt8 :=
  if IOUAmount.operator_ne a b then 1 else 0

@[export lean_iou_lt]
def lean_iou_lt (a b : IOUAmount) (mode : rounding_mode) : Except Error Bool :=
  IOUAmount.operator_lt a b mode

@[export lean_iou_le]
def lean_iou_le (a b : IOUAmount) (mode : rounding_mode) : Except Error Bool :=
  IOUAmount.operator_le a b mode

@[export lean_iou_gt]
def lean_iou_gt (a b : IOUAmount) (mode : rounding_mode) : Except Error Bool :=
  IOUAmount.operator_gt a b mode

@[export lean_iou_ge]
def lean_iou_ge (a b : IOUAmount) (mode : rounding_mode) : Except Error Bool :=
  IOUAmount.operator_ge a b mode

@[export lean_iou_neg]
def lean_iou_neg (a : IOUAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  a.operator_neg mode

@[export lean_iou_add]
def lean_iou_add (a b : IOUAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.operator_add a b mode

@[export lean_iou_sub]
def lean_iou_sub (a b : IOUAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.operator_sub a b mode

@[export lean_iou_mul_ratio]
def lean_iou_mul_ratio (a : IOUAmount) (num den : UInt32) (roundUp : UInt8) (mode : rounding_mode)
    : Except Error IOUAmount :=
  IOUAmount.mulRatio a num den (roundUp != 0) mode

end XRPL.FFI
