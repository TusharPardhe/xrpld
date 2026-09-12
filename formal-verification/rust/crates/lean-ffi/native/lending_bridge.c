#include "lending_bridge.h"
#include <lean/lean.h>
#include <stdlib.h>

extern lean_object *initialize_XRPL_XRPL_FFI_Lending(uint8_t);
extern uint8_t lean_lending_has_expired(uint32_t, uint32_t, uint8_t);
extern lean_object *lean_lending_schedule_build(uint32_t,uint32_t,uint32_t,uint32_t,uint32_t,uint8_t);
extern uint32_t lean_lending_schedule_interval(lean_object *);
extern uint32_t lean_lending_schedule_total(lean_object *);
extern uint32_t lean_lending_schedule_grace(lean_object *);
extern uint32_t lean_lending_schedule_start(lean_object *);
extern uint32_t lean_lending_schedule_time_check(lean_object *);

typedef lean_object *(*wire_fn)(lean_object *);
#define WIRE(name) extern lean_object *name(lean_object *);
WIRE(lean_lending_raw_create_wire) WIRE(lean_lending_raw_create_pending_wire)
WIRE(lean_lending_raw_create_immediate_wire) WIRE(lean_lending_raw_accept_wire)
WIRE(lean_lending_raw_delete_wire) WIRE(lean_lending_raw_regular_payment_wire)
WIRE(lean_lending_raw_late_payment_wire) WIRE(lean_lending_raw_full_payment_wire)
WIRE(lean_lending_raw_manage_impair_wire) WIRE(lean_lending_raw_manage_unimpair_wire)
WIRE(lean_lending_raw_manage_default_wire) WIRE(lean_lending_raw_broker_create_wire)
WIRE(lean_lending_raw_broker_update_wire) WIRE(lean_lending_raw_cover_validate_wire)
WIRE(lean_lending_raw_cover_deposit_wire) WIRE(lean_lending_raw_cover_withdraw_wire)
WIRE(lean_lending_terminal_create_wire) WIRE(lean_lending_terminal_create_pending_wire)
WIRE(lean_lending_terminal_create_immediate_wire) WIRE(lean_lending_terminal_accept_wire)
WIRE(lean_lending_terminal_delete_wire) WIRE(lean_lending_terminal_regular_payment_wire)
WIRE(lean_lending_terminal_late_payment_wire) WIRE(lean_lending_terminal_full_payment_wire)
WIRE(lean_lending_terminal_manage_impair_wire) WIRE(lean_lending_terminal_manage_unimpair_wire)
WIRE(lean_lending_terminal_manage_default_wire)

static wire_fn const wire_routes[] = {
  lean_lending_raw_create_wire, lean_lending_raw_create_pending_wire,
  lean_lending_raw_create_immediate_wire, lean_lending_raw_accept_wire,
  lean_lending_raw_delete_wire, lean_lending_raw_regular_payment_wire,
  lean_lending_raw_late_payment_wire, lean_lending_raw_full_payment_wire,
  lean_lending_raw_manage_impair_wire, lean_lending_raw_manage_unimpair_wire,
  lean_lending_raw_manage_default_wire, lean_lending_raw_broker_create_wire,
  lean_lending_raw_broker_update_wire, lean_lending_raw_cover_validate_wire,
  lean_lending_raw_cover_deposit_wire, lean_lending_raw_cover_withdraw_wire,
  lean_lending_terminal_create_wire, lean_lending_terminal_create_pending_wire,
  lean_lending_terminal_create_immediate_wire, lean_lending_terminal_accept_wire,
  lean_lending_terminal_delete_wire, lean_lending_terminal_regular_payment_wire,
  lean_lending_terminal_late_payment_wire, lean_lending_terminal_full_payment_wire,
  lean_lending_terminal_manage_impair_wire, lean_lending_terminal_manage_unimpair_wire,
  lean_lending_terminal_manage_default_wire,
};
_Static_assert(sizeof wire_routes / sizeof *wire_routes == LEAN_LENDING_RAW_EXPORT_COUNT + LEAN_LENDING_TERMINAL_EXPORT_COUNT, "all wire exports");

static lean_object *retain(lean_object *value) { lean_inc_ref(value); return value; }
static lean_object *bytes_from_copy(const uint8_t *input, size_t size) {
  lean_object *bytes = lean_mk_empty_byte_array(lean_box(size));
  for (size_t i = 0; i < size; ++i) bytes = lean_byte_array_push(bytes, input[i]);
  return bytes;
}
static int copy_result(lean_object *result, uint8_t **out, size_t *out_len) {
  size_t size = lean_unbox(lean_byte_array_size(result));
  uint8_t *copy = malloc(size ? size : 1);
  if (!copy) { lean_dec(result); return 0; }
  for (size_t i = 0; i < size; ++i) copy[i] = lean_byte_array_uget(result, i);
  lean_dec(result); *out = copy; *out_len = size; return 1;
}
static int initialized(lean_object *value) {
  if (lean_io_result_is_error(value)) { lean_dec(value); return 0; }
  lean_dec_ref(value); return 1;
}

int lean_lending_initialize(void) { return initialized(initialize_XRPL_XRPL_FFI_Lending(1)); }
int lean_lending_expired(uint32_t now, uint32_t expiry, uint8_t exclusive) { return lean_lending_has_expired(now, expiry, exclusive); }
int lean_lending_schedule_projection(uint32_t interval, uint32_t total, uint32_t grace,
  uint32_t start, uint32_t now, uint8_t two_step, uint32_t *out) {
  if (!out) return 0;
  lean_object *schedule = lean_lending_schedule_build(interval,total,grace,start,now,two_step);
  out[0] = lean_lending_schedule_interval(retain(schedule));
  out[1] = lean_lending_schedule_total(retain(schedule));
  out[2] = lean_lending_schedule_grace(retain(schedule));
  out[3] = lean_lending_schedule_start(retain(schedule));
  out[4] = lean_lending_schedule_time_check(schedule); return 1;
}
int lean_lending_wire_invoke(uint32_t operation, const uint8_t *input,
  size_t input_len, uint8_t **out, size_t *out_len) {
  if (!out || !out_len || operation == 0 || operation > sizeof wire_routes / sizeof *wire_routes || (!input && input_len)) return 0;
  *out = NULL; *out_len = 0;
  return copy_result(wire_routes[operation - 1](bytes_from_copy(input, input_len)), out, out_len);
}
void lean_lending_wire_free(uint8_t *out) { free(out); }
int lean_lending_complete_adapter(void) {
  const uint8_t malformed[] = { 0 };
  uint8_t *out; size_t out_len; int calls = 0;
  if (!lean_lending_initialize()) return 0;
  (void)lean_lending_has_expired(2,1,0); ++calls;
  lean_object *schedule = lean_lending_schedule_build(60,1,60,10,20,0); ++calls;
  (void)lean_lending_schedule_interval(retain(schedule)); ++calls;
  (void)lean_lending_schedule_total(retain(schedule)); ++calls;
  (void)lean_lending_schedule_grace(retain(schedule)); ++calls;
  (void)lean_lending_schedule_start(retain(schedule)); ++calls;
  (void)lean_lending_schedule_time_check(schedule); ++calls;
  for (uint32_t op = 1; op <= sizeof wire_routes / sizeof *wire_routes; ++op) {
    if (!lean_lending_wire_invoke(op, malformed, sizeof malformed, &out, &out_len)) return 0;
    lean_lending_wire_free(out); ++calls;
  }
  return calls == LEAN_LENDING_EXPORT_COUNT ? calls : 0;
}
