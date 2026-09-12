#include "stamount_bridge.h"
#include <lean/lean.h>
#include <stddef.h>
_Static_assert(sizeof(lean_stamount) == 32, "STAmount ABI");
_Static_assert(_Alignof(lean_stamount) == 8, "STAmount ABI alignment");
_Static_assert(offsetof(lean_stamount, type) == 0, "STAmount type");
_Static_assert(offsetof(lean_stamount, mantissa) == 8, "STAmount mantissa");
_Static_assert(offsetof(lean_stamount, offset) == 16, "STAmount offset");
_Static_assert(offsetof(lean_stamount, negative) == 24, "STAmount negative");
_Static_assert(sizeof(lean_stnumber) == 24, "Number ABI");
_Static_assert(_Alignof(lean_stnumber) == 8, "Number ABI alignment");
_Static_assert(offsetof(lean_stnumber, negative) == 0, "Number negative");
_Static_assert(offsetof(lean_stnumber, mantissa) == 8, "Number mantissa");
_Static_assert(offsetof(lean_stnumber, exponent) == 16, "Number exponent");
extern lean_object* lean_numeric_type_build(uint8_t);
extern lean_object* lean_st_amount_build(lean_object*, uint64_t, uint64_t, uint8_t);
extern lean_object* lean_st_amount_numeric_type(lean_object*);
extern uint64_t lean_st_amount_mantissa(lean_object*), lean_st_amount_offset(lean_object*);
extern uint8_t lean_st_amount_negative(lean_object*), lean_stamount_are_comparable(lean_object*, lean_object*), lean_stamount_eq(lean_object*, lean_object*), lean_stamount_ne(lean_object*, lean_object*);
extern lean_object* lean_stamount_int_amount(lean_object*); extern lean_object* lean_stamount_iou(lean_object*,uint8_t); extern lean_object* lean_stamount_to_number(lean_object*,uint8_t); extern lean_object* lean_stamount_unchecked_from_int64(lean_object*,uint64_t,uint64_t); extern lean_object* lean_stamount_checked(lean_object*,uint64_t,uint64_t,uint8_t,uint8_t); extern lean_object* lean_stamount_of_int64(lean_object*,uint64_t,uint64_t,uint8_t); extern lean_object* lean_stamount_of_number(lean_object*,lean_object*,uint8_t);
extern lean_object* lean_stamount_lt(lean_object*,lean_object*); extern lean_object* lean_stamount_le(lean_object*,lean_object*); extern lean_object* lean_stamount_gt(lean_object*,lean_object*); extern lean_object* lean_stamount_ge(lean_object*,lean_object*); extern lean_object* lean_stamount_neg(lean_object*); extern lean_object* lean_stamount_add(lean_object*,lean_object*,uint8_t); extern lean_object* lean_stamount_sub(lean_object*,lean_object*,uint8_t); extern lean_object* lean_stamount_divide(lean_object*,lean_object*,lean_object*,uint8_t); extern lean_object* lean_stamount_multiply(lean_object*,lean_object*,lean_object*,uint8_t); extern lean_object* lean_stamount_mul_round(lean_object*,lean_object*,lean_object*,uint8_t,uint8_t); extern lean_object* lean_stamount_mul_round_strict(lean_object*,lean_object*,lean_object*,uint8_t,uint8_t); extern lean_object* lean_stamount_div_round(lean_object*,lean_object*,lean_object*,uint8_t,uint8_t); extern lean_object* lean_stamount_div_round_strict(lean_object*,lean_object*,lean_object*,uint8_t,uint8_t); extern lean_object* lean_stamount_can_add(lean_object*,lean_object*,uint8_t); extern lean_object* lean_stamount_can_subtract(lean_object*,lean_object*); extern lean_object* lean_stamount_round_to_exponent(lean_object*,uint64_t,uint8_t);
extern uint64_t lean_stamount_get_rate(lean_object*, lean_object*, uint8_t);
extern uint64_t lean_iou_amount_mantissa(lean_object*), lean_iou_amount_exponent(lean_object*);
extern lean_object* lean_number_build_norm(uint8_t, uint64_t, uint64_t);
extern uint8_t lean_number_negative(lean_object*); extern uint64_t lean_number_mantissa(lean_object*), lean_number_exponent(lean_object*);
static lean_object* keep(lean_object* x) { lean_inc(x); return x; }
static uint8_t err(lean_object* x) { return lean_is_scalar(x) ? (uint8_t)lean_unbox(x) : (uint8_t)lean_obj_tag(x); }
static lean_object* st(lean_stamount x) { return lean_st_amount_build(lean_numeric_type_build(x.type), x.mantissa, (uint64_t)x.offset, x.negative); }
static void read_st(lean_object* x, lean_stamount* out) { lean_object* nt = lean_st_amount_numeric_type(keep(x)); out->type = nt == lean_numeric_type_build(0) ? 0 : nt == lean_numeric_type_build(1) ? 1 : 2; lean_dec(nt); out->mantissa = lean_st_amount_mantissa(keep(x)); out->offset = (int64_t)lean_st_amount_offset(keep(x)); out->negative = lean_st_amount_negative(x); }
static void read_num(lean_object* x, lean_stnumber* out) { out->negative = lean_number_negative(keep(x)); out->mantissa = lean_number_mantissa(keep(x)); out->exponent = (int64_t)lean_number_exponent(x); }
static int result_st(lean_object* r, lean_stamount* out, uint8_t* e) { if (lean_obj_tag(r) != 1) { *e = err(lean_ctor_get(r, 0)); lean_dec(r); return 0; } read_st(keep(lean_ctor_get(r, 0)), out); lean_dec(r); return 1; }
static int result_bool(lean_object* r, uint8_t* out, uint8_t* e) { if (lean_obj_tag(r) != 1) { *e = err(lean_ctor_get(r, 0)); lean_dec(r); return 0; } *out = lean_unbox(lean_ctor_get(r, 0)); lean_dec(r); return 1; }
void lean_st_access(lean_stamount x, lean_stamount* out) { read_st(st(x), out); }
uint8_t lean_st_comparable(lean_stamount a, lean_stamount b) { return lean_stamount_are_comparable(st(a), st(b)); }
int lean_st_int(lean_stamount x, int64_t* out, uint8_t* e) { lean_object* r = lean_stamount_int_amount(st(x)); if (lean_obj_tag(r) != 1) { *e=err(lean_ctor_get(r,0)); lean_dec(r); return 0; } *out=(int64_t)lean_unbox_uint64(lean_ctor_get(r,0)); lean_dec(r); return 1; }
int lean_st_iou(lean_stamount x, uint8_t m, int64_t* a, int64_t* b, uint8_t* e) { lean_object* r=lean_stamount_iou(st(x),m); if(lean_obj_tag(r)!=1){*e=err(lean_ctor_get(r,0));lean_dec(r);return 0;} lean_object* v=keep(lean_ctor_get(r,0)); *a=(int64_t)lean_iou_amount_mantissa(keep(v)); *b=(int64_t)lean_iou_amount_exponent(v); lean_dec(r);return 1; }
int lean_st_number(lean_stamount x,uint8_t m,lean_stnumber* o,uint8_t* e){lean_object*r=lean_stamount_to_number(st(x),m);if(lean_obj_tag(r)!=1){*e=err(lean_ctor_get(r,0));lean_dec(r);return 0;}read_num(keep(lean_ctor_get(r,0)),o);lean_dec(r);return 1;}
int lean_st_construct(uint8_t op,lean_stamount x,int64_t v,lean_stnumber n,uint8_t m,lean_stamount*o,uint8_t*e){lean_object*r; if(op==0){read_st(lean_stamount_unchecked_from_int64(lean_numeric_type_build(x.type),(uint64_t)v,(uint64_t)x.offset),o);return 1;}if(op==1)r=lean_stamount_checked(lean_numeric_type_build(x.type),x.mantissa,(uint64_t)x.offset,x.negative,m);else if(op==2)r=lean_stamount_of_int64(lean_numeric_type_build(x.type),(uint64_t)v,(uint64_t)x.offset,m);else if(op==3)r=lean_stamount_of_number(lean_numeric_type_build(x.type),lean_number_build_norm(n.negative,n.mantissa,(uint64_t)n.exponent),m);else {*e=255;return 0;}return result_st(r,o,e);}
uint8_t lean_st_eq(uint8_t op,lean_stamount a,lean_stamount b){return op?lean_stamount_ne(st(a),st(b)):lean_stamount_eq(st(a),st(b));}
int lean_st_compare(uint8_t op,lean_stamount a,lean_stamount b,uint8_t*o,uint8_t*e){lean_object*l=st(a),*r=st(b),*z;switch(op){case 0:z=lean_stamount_lt(l,r);break;case 1:z=lean_stamount_le(l,r);break;case 2:z=lean_stamount_gt(l,r);break;case 3:z=lean_stamount_ge(l,r);break;default:lean_dec(l);lean_dec(r);*e=255;return 0;}return result_bool(z,o,e);}
void lean_st_neg(lean_stamount x,lean_stamount*o){read_st(lean_stamount_neg(st(x)),o);}
int lean_st_binary(uint8_t op,lean_stamount a,lean_stamount b,uint8_t t,uint8_t up,uint8_t m,lean_stamount*o,uint8_t*e){lean_object*l=st(a),*r=st(b),*z,*nt=lean_numeric_type_build(t);switch(op){case 0:z=lean_stamount_add(l,r,m);break;case 1:z=lean_stamount_sub(l,r,m);break;case 2:z=lean_stamount_divide(l,r,nt,m);break;case 3:z=lean_stamount_multiply(l,r,nt,m);break;case 4:z=lean_stamount_mul_round(l,r,nt,up,m);break;case 5:z=lean_stamount_mul_round_strict(l,r,nt,up,m);break;case 6:z=lean_stamount_div_round(l,r,nt,up,m);break;case 7:z=lean_stamount_div_round_strict(l,r,nt,up,m);break;default:lean_dec(l);lean_dec(r);lean_dec(nt);*e=255;return 0;}return result_st(z,o,e);}
int lean_st_can(uint8_t op,lean_stamount a,lean_stamount b,uint8_t m,uint8_t*o,uint8_t*e){return result_bool(op?lean_stamount_can_subtract(st(a),st(b)):lean_stamount_can_add(st(a),st(b),m),o,e);}
int lean_st_round(lean_stamount x,int64_t s,uint8_t m,lean_stamount*o,uint8_t*e){return result_st(lean_stamount_round_to_exponent(st(x),(uint64_t)s,m),o,e);}
uint64_t lean_st_rate(lean_stamount a,lean_stamount b,uint8_t m){return lean_stamount_get_rate(st(a),st(b),m);}
