import XRPL.FFI.CommonFFI
import XRPL.Model.Protocol.STAmount


namespace XRPL.FFI

open XRPL.Model.Protocol

@[export lean_st_amount_build]
def lean_st_amount_build (numericType : NumericType) (mantissa : UInt64) (offset : Int64)
    (negative : UInt8) : STAmount :=
  STAmount.unchecked numericType mantissa offset.toInt (negative != 0)
@[export lean_st_amount_numeric_type]
def lean_st_amount_numeric_type (s : STAmount) : NumericType := s.numericType
@[export lean_st_amount_mantissa]
def lean_st_amount_mantissa (s : STAmount) : UInt64 := s.mantissa
@[export lean_st_amount_offset]
def lean_st_amount_offset (s : STAmount) : Int64 := s.exponent.toInt64
@[export lean_st_amount_negative]
def lean_st_amount_negative (s : STAmount) : UInt8 := if s.negative then 1 else 0

@[export lean_stamount_are_comparable]
def lean_stamount_are_comparable (a b : STAmount) : UInt8 :=
  if STAmount.areComparable a b then 1 else 0

-- Integral (XRP/MPT) view as a plain int64. Merged from the old xrp/mpt accessors.
@[export lean_stamount_int_amount]
def lean_stamount_int_amount (s : STAmount) : Except Error Int64 :=
  s.intAmount.map (·.value)

@[export lean_stamount_iou]
def lean_stamount_iou (s : STAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  s.iou mode

@[export lean_stamount_to_number]
def lean_stamount_to_number (s : STAmount) (mode : rounding_mode) : Except Error Number :=
  s.toNumber mode

@[export lean_stamount_unchecked_from_int64]
def lean_stamount_unchecked_from_int64 (numericType : NumericType) (v : Int64) (offset : Int64)
    : STAmount :=
  STAmount.uncheckedFromInt64 numericType v offset.toInt

@[export lean_stamount_checked]
def lean_stamount_checked (numericType : NumericType) (mValue : UInt64) (mOffset : Int64)
    (mIsNegative : UInt8) (mode : rounding_mode) : Except Error STAmount :=
  STAmount.checked numericType mValue mOffset.toInt (mIsNegative != 0)
    mode

@[export lean_stamount_of_int64]
def lean_stamount_of_int64 (numericType : NumericType) (mantissa : Int64) (exponent : Int64)
    (mode : rounding_mode) : Except Error STAmount :=
  STAmount.ofInt64 numericType mantissa exponent.toInt mode

@[export lean_stamount_of_number]
def lean_stamount_of_number (numericType : NumericType) (n : Number) (mode : rounding_mode)
    : Except Error STAmount :=
  STAmount.ofNumber numericType n mode

@[export lean_stamount_eq]
def lean_stamount_eq (a b : STAmount) : UInt8 :=
  if STAmount.operator_eq a b then 1 else 0

@[export lean_stamount_ne]
def lean_stamount_ne (a b : STAmount) : UInt8 :=
  if STAmount.operator_ne a b then 1 else 0

@[export lean_stamount_lt]
def lean_stamount_lt (a b : STAmount) : Except Error Bool :=
  STAmount.operator_lt a b

@[export lean_stamount_le]
def lean_stamount_le (a b : STAmount) : Except Error Bool :=
  STAmount.operator_le a b

@[export lean_stamount_gt]
def lean_stamount_gt (a b : STAmount) : Except Error Bool :=
  STAmount.operator_gt a b

@[export lean_stamount_ge]
def lean_stamount_ge (a b : STAmount) : Except Error Bool :=
  STAmount.operator_ge a b

@[export lean_stamount_neg]
def lean_stamount_neg (s : STAmount) : STAmount := s.operator_neg

@[export lean_stamount_add]
def lean_stamount_add (a b : STAmount) (mode : rounding_mode) : Except Error STAmount :=
  STAmount.operator_add a b mode

@[export lean_stamount_sub]
def lean_stamount_sub (a b : STAmount) (mode : rounding_mode) : Except Error STAmount :=
  STAmount.operator_sub a b mode

@[export lean_stamount_divide]
def lean_stamount_divide (num den : STAmount) (numericType : NumericType) (mode : rounding_mode)
    : Except Error STAmount :=
  STAmount.divide num den numericType mode

@[export lean_stamount_multiply]
def lean_stamount_multiply (v1 v2 : STAmount) (numericType : NumericType) (mode : rounding_mode)
    : Except Error STAmount :=
  STAmount.multiply v1 v2 numericType mode

@[export lean_stamount_mul_round]
def lean_stamount_mul_round (v1 v2 : STAmount) (numericType : NumericType) (roundUp : UInt8)
    (mode : rounding_mode) : Except Error STAmount :=
  STAmount.mulRound v1 v2 numericType (roundUp != 0) mode

@[export lean_stamount_mul_round_strict]
def lean_stamount_mul_round_strict (v1 v2 : STAmount) (numericType : NumericType) (roundUp : UInt8)
    (mode : rounding_mode) : Except Error STAmount :=
  STAmount.mulRoundStrict v1 v2 numericType (roundUp != 0) mode

@[export lean_stamount_div_round]
def lean_stamount_div_round (num den : STAmount) (numericType : NumericType) (roundUp : UInt8)
    (mode : rounding_mode) : Except Error STAmount :=
  STAmount.divRound num den numericType (roundUp != 0) mode

@[export lean_stamount_div_round_strict]
def lean_stamount_div_round_strict (num den : STAmount) (numericType : NumericType) (roundUp : UInt8)
    (mode : rounding_mode) : Except Error STAmount :=
  STAmount.divRoundStrict num den numericType (roundUp != 0) mode

@[export lean_stamount_can_add]
def lean_stamount_can_add (a b : STAmount) (mode : rounding_mode) : Except Error Bool :=
  STAmount.canAdd a b mode

@[export lean_stamount_can_subtract]
def lean_stamount_can_subtract (a b : STAmount) : Except Error Bool :=
  STAmount.canSubtract a b

-- Matches C++ `roundToScale`.
@[export lean_stamount_round_to_exponent]
def lean_stamount_round_to_exponent (s : STAmount) (scale : Int64) (mode : rounding_mode)
    : Except Error STAmount :=
  STAmount.roundToExponent s scale.toInt mode

@[export lean_stamount_get_rate]
def lean_stamount_get_rate (offerOut offerIn : STAmount) (mode : rounding_mode) : UInt64 :=
  STAmount.getRate offerOut offerIn mode

end XRPL.FFI
