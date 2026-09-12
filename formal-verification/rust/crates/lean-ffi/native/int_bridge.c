#include "int_bridge.h"
#include <lean/lean.h>
#include <stddef.h>

_Static_assert(sizeof(lean_int_number) == 24, "Number ABI size");
_Static_assert(_Alignof(lean_int_number) == 8, "Number ABI alignment");
_Static_assert(offsetof(lean_int_number, negative) == 0, "Number ABI negative");
_Static_assert(offsetof(lean_int_number, mantissa) == 8, "Number ABI mantissa");
_Static_assert(offsetof(lean_int_number, exponent) == 16, "Number ABI exponent");
/* Generated IntAmountFFI.c is authoritative: Lean Int64 uses uint64_t bits. */
extern lean_object* lean_number_build_norm(uint8_t, uint64_t, uint64_t);
extern uint8_t lean_number_negative(lean_object*);
extern uint64_t lean_number_mantissa(lean_object*);
extern uint64_t lean_number_exponent(lean_object*);
extern uint64_t lean_int_amount_of_int64(uint64_t);
extern lean_object* lean_int_amount_of_number(lean_object*, uint8_t);
extern lean_object* lean_int_amount_to_number(uint64_t, uint8_t);
extern uint8_t lean_int_amount_eq(uint64_t, uint64_t);
extern uint8_t lean_int_amount_ne(uint64_t, uint64_t);
extern uint8_t lean_int_amount_eq_int(uint64_t, uint64_t);
extern uint8_t lean_int_amount_ne_int(uint64_t, uint64_t);
extern uint8_t lean_int_amount_lt(uint64_t, uint64_t);
extern uint8_t lean_int_amount_le(uint64_t, uint64_t);
extern uint8_t lean_int_amount_gt(uint64_t, uint64_t);
extern uint8_t lean_int_amount_ge(uint64_t, uint64_t);
extern uint64_t lean_int_amount_add(uint64_t, uint64_t);
extern uint64_t lean_int_amount_sub(uint64_t, uint64_t);
extern uint64_t lean_int_amount_neg(uint64_t);
extern uint64_t lean_int_amount_mul(uint64_t, uint64_t);
extern uint64_t lean_int_amount_add_int(uint64_t, uint64_t);
extern uint64_t lean_int_amount_sub_int(uint64_t, uint64_t);
extern lean_object* lean_int_amount_mul_ratio(uint64_t, uint32_t, uint32_t, uint8_t);

static lean_object* keep(lean_object* value) { lean_inc(value); return value; }
static uint8_t error_tag(lean_object* error) {
  return lean_is_scalar(error) ? (uint8_t)lean_unbox(error) : (uint8_t)lean_obj_tag(error);
}
static lean_object* number(lean_int_number value) {
  return lean_number_build_norm(value.negative, value.mantissa, (uint64_t)value.exponent);
}
static void read_number(lean_object* owned, lean_int_number* out) {
  out->negative = lean_number_negative(keep(owned));
  out->mantissa = lean_number_mantissa(keep(owned));
  out->exponent = (int64_t)lean_number_exponent(owned);
}
static int read_int_result(lean_object* result, uint64_t* out, uint8_t* error) {
  if (lean_obj_tag(result) != 1) {
    *error = error_tag(lean_ctor_get(result, 0));
    lean_dec(result);
    return 0;
  }
  *out = lean_unbox_uint64(lean_ctor_get(result, 0));
  lean_dec(result);
  return 1;
}
static int read_number_result(lean_object* result, lean_int_number* out, uint8_t* error) {
  if (lean_obj_tag(result) != 1) {
    *error = error_tag(lean_ctor_get(result, 0));
    lean_dec(result);
    return 0;
  }
  read_number(keep(lean_ctor_get(result, 0)), out);
  lean_dec(result);
  return 1;
}

uint64_t lean_int_direct(uint8_t op, uint64_t left, uint64_t right) {
  switch (op) {
    case 0: return lean_int_amount_of_int64(left);
    case 1: return lean_int_amount_add(left, right);
    case 2: return lean_int_amount_sub(left, right);
    case 3: return lean_int_amount_neg(left);
    case 4: return lean_int_amount_mul(left, right);
    case 5: return lean_int_amount_add_int(left, right);
    case 6: return lean_int_amount_sub_int(left, right);
    default: return UINT64_MAX;
  }
}
uint8_t lean_int_compare(uint8_t relation, uint64_t left, uint64_t right) {
  switch (relation) {
    case 0: return lean_int_amount_eq(left, right);
    case 1: return lean_int_amount_ne(left, right);
    case 2: return lean_int_amount_eq_int(left, right);
    case 3: return lean_int_amount_ne_int(left, right);
    case 4: return lean_int_amount_lt(left, right);
    case 5: return lean_int_amount_le(left, right);
    case 6: return lean_int_amount_gt(left, right);
    case 7: return lean_int_amount_ge(left, right);
    default: return UINT8_MAX;
  }
}
int lean_int_from_number(lean_int_number value, uint8_t mode, uint64_t* out, uint8_t* error) {
  return read_int_result(lean_int_amount_of_number(number(value), mode), out, error);
}
int lean_int_to_number(uint64_t value, uint8_t mode, lean_int_number* out, uint8_t* error) {
  return read_number_result(lean_int_amount_to_number(value, mode), out, error);
}
int lean_int_mul_ratio(uint64_t value, uint32_t num, uint32_t den, uint8_t round_up,
                       uint64_t* out, uint8_t* error) {
  return read_int_result(lean_int_amount_mul_ratio(value, num, den, round_up), out, error);
}
