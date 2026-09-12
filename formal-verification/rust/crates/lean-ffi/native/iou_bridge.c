#include "iou_bridge.h"
#include <lean/lean.h>
#include <stddef.h>

_Static_assert(sizeof(lean_bridge_iou) == 16, "IOU ABI size");
_Static_assert(_Alignof(lean_bridge_iou) == 8, "IOU ABI alignment");
_Static_assert(offsetof(lean_bridge_iou, mantissa) == 0, "IOU mantissa ABI");
_Static_assert(offsetof(lean_bridge_iou, exponent) == 8, "IOU exponent ABI");
_Static_assert(sizeof(lean_bridge_number) == 24, "Number ABI size");
_Static_assert(_Alignof(lean_bridge_number) == 8, "Number ABI alignment");
_Static_assert(offsetof(lean_bridge_number, negative) == 0, "Number ABI negative");
_Static_assert(offsetof(lean_bridge_number, mantissa) == 8, "Number ABI mantissa");
_Static_assert(offsetof(lean_bridge_number, exponent) == 16, "Number ABI exponent");
extern lean_object* lean_number_build_norm(uint8_t, uint64_t, uint64_t);
extern uint8_t lean_number_negative(lean_object*);
extern uint64_t lean_number_mantissa(lean_object*);
extern uint64_t lean_number_exponent(lean_object*);
extern lean_object* lean_iou_amount_build(uint64_t, uint64_t);
extern uint64_t lean_iou_amount_mantissa(lean_object*);
extern uint64_t lean_iou_amount_exponent(lean_object*);
extern lean_object* lean_iou_from_number(lean_object*, uint8_t);
extern lean_object* lean_iou_of_mantissa_exp(uint64_t, uint64_t, uint8_t);
extern lean_object* lean_iou_of_number(lean_object*, uint8_t);
extern lean_object* lean_iou_to_number(lean_object*, uint8_t);
extern uint8_t lean_iou_eq(lean_object*, lean_object*);
extern uint8_t lean_iou_ne(lean_object*, lean_object*);
extern lean_object* lean_iou_lt(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_iou_le(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_iou_gt(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_iou_ge(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_iou_neg(lean_object*, uint8_t);
extern lean_object* lean_iou_add(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_iou_sub(lean_object*, lean_object*, uint8_t);
extern lean_object* lean_iou_mul_ratio(lean_object*, uint32_t, uint32_t, uint8_t, uint8_t);

static lean_object* keep(lean_object* value) { lean_inc(value); return value; }
static uint8_t error_tag(lean_object* error) { return lean_is_scalar(error) ? (uint8_t)lean_unbox(error) : (uint8_t)lean_obj_tag(error); }
static lean_object* number(lean_bridge_number x) { return lean_number_build_norm(x.negative, x.mantissa, (uint64_t)x.exponent); }
static lean_object* iou(lean_bridge_iou x) { return lean_iou_amount_build((uint64_t)x.mantissa, (uint64_t)x.exponent); }
static void read_iou(lean_object* owned, lean_bridge_iou* out) { out->mantissa = (int64_t)lean_iou_amount_mantissa(keep(owned)); out->exponent = (int64_t)lean_iou_amount_exponent(owned); }
static void read_number(lean_object* owned, lean_bridge_number* out) { out->negative = lean_number_negative(keep(owned)); out->mantissa = lean_number_mantissa(keep(owned)); out->exponent = (int64_t)lean_number_exponent(owned); }
static int read_iou_result(lean_object* result, lean_bridge_iou* out, uint8_t* error) { if (lean_obj_tag(result) != 1) { *error = error_tag(lean_ctor_get(result, 0)); lean_dec(result); return 0; } read_iou(keep(lean_ctor_get(result, 0)), out); lean_dec(result); return 1; }
static int read_number_result(lean_object* result, lean_bridge_number* out, uint8_t* error) { if (lean_obj_tag(result) != 1) { *error = error_tag(lean_ctor_get(result, 0)); lean_dec(result); return 0; } read_number(keep(lean_ctor_get(result, 0)), out); lean_dec(result); return 1; }
static uint8_t read_bool_result(lean_object* result, uint8_t* error) { if (lean_obj_tag(result) != 1) { *error = error_tag(lean_ctor_get(result, 0)); lean_dec(result); return UINT8_MAX; } uint8_t value = lean_unbox(lean_ctor_get(result, 0)); lean_dec(result); return value; }

void lean_iou_build_accessors(int64_t mantissa, int64_t exponent, lean_bridge_iou* out) { read_iou(lean_iou_amount_build((uint64_t)mantissa, (uint64_t)exponent), out); }
int lean_iou_from_number_bridge(lean_bridge_number x, uint8_t mode, lean_bridge_iou* out, uint8_t* error) { return read_iou_result(lean_iou_from_number(number(x), mode), out, error); }
int lean_iou_of_mantissa_exp_bridge(int64_t m, int64_t e, uint8_t mode, lean_bridge_iou* out, uint8_t* error) { return read_iou_result(lean_iou_of_mantissa_exp((uint64_t)m, (uint64_t)e, mode), out, error); }
int lean_iou_of_number_bridge(lean_bridge_number x, uint8_t mode, lean_bridge_iou* out, uint8_t* error) { return read_iou_result(lean_iou_of_number(number(x), mode), out, error); }
int lean_iou_to_number_bridge(lean_bridge_iou x, uint8_t mode, lean_bridge_number* out, uint8_t* error) { return read_number_result(lean_iou_to_number(iou(x), mode), out, error); }
uint8_t lean_iou_compare_bridge(uint8_t rel, lean_bridge_iou a, lean_bridge_iou b, uint8_t mode, uint8_t* error) { lean_object* l = iou(a); lean_object* r = iou(b); switch (rel) { case 0: lean_dec(r); lean_dec(l); return lean_iou_eq(iou(a), iou(b)); case 1: lean_dec(r); lean_dec(l); return lean_iou_ne(iou(a), iou(b)); case 2: return read_bool_result(lean_iou_lt(l, r, mode), error); case 3: return read_bool_result(lean_iou_le(l, r, mode), error); case 4: return read_bool_result(lean_iou_gt(l, r, mode), error); case 5: return read_bool_result(lean_iou_ge(l, r, mode), error); default: lean_dec(l); lean_dec(r); *error = UINT8_MAX; return UINT8_MAX; } }
int lean_iou_unary_bridge(uint8_t op, lean_bridge_iou x, uint8_t mode, lean_bridge_iou* out, uint8_t* error) { if (op != 0) { *error = UINT8_MAX; return 0; } return read_iou_result(lean_iou_neg(iou(x), mode), out, error); }
int lean_iou_binary_bridge(uint8_t op, lean_bridge_iou a, lean_bridge_iou b, uint8_t mode, lean_bridge_iou* out, uint8_t* error) { lean_object* l = iou(a); lean_object* r = iou(b); if (op == 0) return read_iou_result(lean_iou_add(l, r, mode), out, error); if (op == 1) return read_iou_result(lean_iou_sub(l, r, mode), out, error); lean_dec(l); lean_dec(r); *error = UINT8_MAX; return 0; }
int lean_iou_mul_ratio_bridge(lean_bridge_iou x, uint32_t n, uint32_t d, uint8_t up, uint8_t mode, lean_bridge_iou* out, uint8_t* error) { return read_iou_result(lean_iou_mul_ratio(iou(x), n, d, up, mode), out, error); }
