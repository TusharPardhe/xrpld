#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

typedef struct { uint8_t negative; uint64_t mantissa; int64_t exponent; } lean_bridge_number;
_Static_assert(sizeof(lean_bridge_number) == 24, "Number ABI size");
_Static_assert(_Alignof(lean_bridge_number) == 8, "Number ABI alignment");
_Static_assert(offsetof(lean_bridge_number, negative) == 0, "Number ABI negative");
_Static_assert(offsetof(lean_bridge_number, mantissa) == 8, "Number ABI mantissa");
_Static_assert(offsetof(lean_bridge_number, exponent) == 16, "Number ABI exponent");
/* Generated .lake/build/ir ABI authority: Lean Int64 is uint64_t, initializers take one uint8_t. */
extern void lean_initialize_runtime_module(void);
extern lean_object* initialize_XRPL_XRPL_FFI_FFI(uint8_t);
extern lean_object* initialize_XRPL_XRPL_FFI_CommonFFI(uint8_t);
extern lean_object* initialize_XRPL_XRPL_FFI_Protocol_NumberFFI(uint8_t);
extern lean_object* initialize_XRPL_XRPL_FFI_Protocol_IOUAmountFFI(uint8_t);
extern lean_object* initialize_XRPL_XRPL_FFI_Protocol_IntAmountFFI(uint8_t);
extern lean_object* initialize_XRPL_XRPL_FFI_Protocol_STAmountFFI(uint8_t);
extern lean_object* initialize_XRPL_XRPL_FFI_Protocol_NumericTypeFFI(uint8_t);
extern lean_object* lean_number_build(uint8_t, uint64_t, uint64_t);
extern lean_object* lean_number_build_norm(uint8_t, uint64_t, uint64_t);
extern uint8_t lean_number_negative(lean_object*);
extern uint64_t lean_number_mantissa(lean_object*);
extern uint64_t lean_number_exponent(lean_object*);
extern lean_object* lean_number_add(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_number_sub(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_number_mul(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_number_div(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_number_neg(lean_object*);
extern lean_object* lean_number_normalize(lean_object*, uint8_t);
extern lean_object* lean_number_to_rep(lean_object*, uint8_t);
extern uint64_t lean_number_signum(lean_object*);
extern uint8_t lean_number_eq(lean_object*, lean_object*);
extern uint8_t lean_number_ne(lean_object*, lean_object*);
extern uint8_t lean_number_lt(lean_object*, lean_object*);
extern uint8_t lean_number_le(lean_object*, lean_object*);
extern uint8_t lean_number_gt(lean_object*, lean_object*);
extern uint8_t lean_number_ge(lean_object*, lean_object*);
extern uint8_t lean_rounding_mode_build(uint8_t);
extern lean_object* lean_numeric_type_build(uint8_t);
extern uint8_t lean_numeric_type_is_integral(lean_object*);

static lean_object* keep(lean_object* value) { lean_inc(value); return value; }
static void decode_number(lean_object* owned, lean_bridge_number* out) {
  out->negative = lean_number_negative(keep(owned));
  out->mantissa = lean_number_mantissa(keep(owned));
  out->exponent = (int64_t)lean_number_exponent(keep(owned));
  lean_dec(owned);
}
static uint8_t error_tag(lean_object* error) {
  return lean_is_scalar(error) ? (uint8_t)lean_unbox(error) : (uint8_t)lean_obj_tag(error);
}
static int decode_number_except(lean_object* result, lean_bridge_number* out, uint8_t* error) {
  if (lean_obj_tag(result) != 1) { *error = error_tag(lean_ctor_get(result, 0)); lean_dec(result); return 0; }
  lean_object* value = keep(lean_ctor_get(result, 0)); lean_dec(result); decode_number(value, out); return 1;
}
static int decode_i64_except(lean_object* result, int64_t* out, uint8_t* error) {
  if (lean_obj_tag(result) != 1) { *error = error_tag(lean_ctor_get(result, 0)); lean_dec(result); return 0; }
  *out = (int64_t)lean_unbox_uint64(lean_ctor_get(result, 0)); lean_dec(result); return 1;
}
static lean_object* make_number(lean_bridge_number value, int normalized) {
  return normalized ? lean_number_build_norm(value.negative, value.mantissa, (uint64_t)value.exponent) : lean_number_build(value.negative, value.mantissa, (uint64_t)value.exponent);
}
static int init_module(lean_object* result) {
  if (lean_io_result_is_error(result)) { lean_dec(result); return 0; } lean_dec_ref(result); return 1;
}
int lean_bridge_initialize(void) {
  lean_initialize_runtime_module();
  if (!init_module(initialize_XRPL_XRPL_FFI_FFI(1)) || !init_module(initialize_XRPL_XRPL_FFI_CommonFFI(1)) || !init_module(initialize_XRPL_XRPL_FFI_Protocol_NumberFFI(1)) || !init_module(initialize_XRPL_XRPL_FFI_Protocol_IOUAmountFFI(1)) || !init_module(initialize_XRPL_XRPL_FFI_Protocol_IntAmountFFI(1)) || !init_module(initialize_XRPL_XRPL_FFI_Protocol_STAmountFFI(1)) || !init_module(initialize_XRPL_XRPL_FFI_Protocol_NumericTypeFFI(1))) return 0;
  lean_io_mark_end_initialization(); return 1;
}
void lean_bridge_raw_roundtrip(uint8_t negative, uint64_t mantissa, int64_t exponent, lean_bridge_number* out) { decode_number(lean_number_build(negative, mantissa, (uint64_t)exponent), out); }
void lean_bridge_roundtrip(uint8_t negative, uint64_t mantissa, int64_t exponent, lean_bridge_number* out) { decode_number(lean_number_build_norm(negative, mantissa, (uint64_t)exponent), out); }
int lean_bridge_binary(uint8_t op, lean_bridge_number lhs, lean_bridge_number rhs, uint8_t mode, lean_bridge_number* out, uint8_t* error) {
  lean_object* left = make_number(lhs, 1); lean_object* right = make_number(rhs, 1); lean_object* result;
  switch (op) { case 0: result = lean_number_add(left, right, mode); break; case 1: result = lean_number_sub(left, right, mode); break; case 2: result = lean_number_mul(left, right, mode); break; case 3: result = lean_number_div(left, right, mode); break; default: lean_dec(left); lean_dec(right); *error = UINT8_MAX; return 0; }
  return decode_number_except(result, out, error);
}
void lean_bridge_neg(lean_bridge_number value, lean_bridge_number* out) { decode_number(lean_number_neg(make_number(value, 1)), out); }
int64_t lean_bridge_signum(lean_bridge_number value) { return (int64_t)lean_number_signum(make_number(value, 1)); }
uint8_t lean_bridge_compare(uint8_t relation, lean_bridge_number lhs, lean_bridge_number rhs) {
  lean_object* left = make_number(lhs, 1); lean_object* right = make_number(rhs, 1);
  switch (relation) { case 0: return lean_number_eq(left, right); case 1: return lean_number_ne(left, right); case 2: return lean_number_lt(left, right); case 3: return lean_number_le(left, right); case 4: return lean_number_gt(left, right); case 5: return lean_number_ge(left, right); default: lean_dec(left); lean_dec(right); return UINT8_MAX; }
}
int lean_bridge_normalize(lean_bridge_number value, uint8_t mode, lean_bridge_number* out, uint8_t* error) { return decode_number_except(lean_number_normalize(make_number(value, 0), mode), out, error); }
int lean_bridge_to_rep(lean_bridge_number value, uint8_t mode, int64_t* out, uint8_t* error) { return decode_i64_except(lean_number_to_rep(make_number(value, 1), mode), out, error); }
uint8_t lean_bridge_rounding_tag(uint8_t mode) { return lean_rounding_mode_build(mode); }
uint8_t lean_bridge_numeric_integral(uint8_t tag) { return lean_numeric_type_is_integral(lean_numeric_type_build(tag)); }
