#ifndef LENDING_BRIDGE_H
#define LENDING_BRIDGE_H

#include <stddef.h>
#include <stdint.h>

#define LEAN_LENDING_ABI_VERSION 1u
#define LEAN_LENDING_EXPORT_COUNT 34u
#define LEAN_LENDING_RAW_EXPORT_COUNT 16u
#define LEAN_LENDING_TERMINAL_EXPORT_COUNT 11u
#define LEAN_LENDING_SCALAR_EXPORT_COUNT 7u

enum lean_lending_wire_operation {
  LEAN_LENDING_RAW_CREATE = 1, LEAN_LENDING_RAW_CREATE_PENDING,
  LEAN_LENDING_RAW_CREATE_IMMEDIATE, LEAN_LENDING_RAW_ACCEPT,
  LEAN_LENDING_RAW_DELETE, LEAN_LENDING_RAW_REGULAR_PAYMENT,
  LEAN_LENDING_RAW_LATE_PAYMENT, LEAN_LENDING_RAW_FULL_PAYMENT,
  LEAN_LENDING_RAW_MANAGE_IMPAIR, LEAN_LENDING_RAW_MANAGE_UNIMPAIR,
  LEAN_LENDING_RAW_MANAGE_DEFAULT, LEAN_LENDING_RAW_BROKER_CREATE,
  LEAN_LENDING_RAW_BROKER_UPDATE, LEAN_LENDING_RAW_COVER_VALIDATE,
  LEAN_LENDING_RAW_COVER_DEPOSIT, LEAN_LENDING_RAW_COVER_WITHDRAW,
  LEAN_LENDING_TERMINAL_CREATE, LEAN_LENDING_TERMINAL_CREATE_PENDING,
  LEAN_LENDING_TERMINAL_CREATE_IMMEDIATE, LEAN_LENDING_TERMINAL_ACCEPT,
  LEAN_LENDING_TERMINAL_DELETE, LEAN_LENDING_TERMINAL_REGULAR_PAYMENT,
  LEAN_LENDING_TERMINAL_LATE_PAYMENT, LEAN_LENDING_TERMINAL_FULL_PAYMENT,
  LEAN_LENDING_TERMINAL_MANAGE_IMPAIR, LEAN_LENDING_TERMINAL_MANAGE_UNIMPAIR,
  LEAN_LENDING_TERMINAL_MANAGE_DEFAULT,
};

int lean_lending_initialize(void);
int lean_lending_expired(uint32_t now, uint32_t expiry, uint8_t exclusive);
int lean_lending_schedule_projection(uint32_t interval, uint32_t total, uint32_t grace,
  uint32_t start, uint32_t now, uint8_t two_step, uint32_t *out);

/* Copies input into an owned Lean ByteArray and copies the returned ByteArray
 * into malloc-owned memory. Call lean_lending_wire_free exactly once on out. */
int lean_lending_wire_invoke(uint32_t operation, const uint8_t *input,
  size_t input_len, uint8_t **out, size_t *out_len);
void lean_lending_wire_free(uint8_t *out);

/* Initializes and invokes all seven scalar and all 27 wire exports. */
int lean_lending_complete_adapter(void);
#endif
