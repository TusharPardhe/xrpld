#ifndef INT_BRIDGE_H
#define INT_BRIDGE_H

#include <stdint.h>

typedef struct {
  uint8_t negative;
  uint64_t mantissa;
  int64_t exponent;
} lean_int_number;

uint64_t lean_int_direct(uint8_t op, uint64_t left, uint64_t right);
uint8_t lean_int_compare(uint8_t relation, uint64_t left, uint64_t right);
int lean_int_from_number(lean_int_number value, uint8_t mode, uint64_t* out, uint8_t* error);
int lean_int_to_number(uint64_t value, uint8_t mode, lean_int_number* out, uint8_t* error);
int lean_int_mul_ratio(uint64_t value, uint32_t num, uint32_t den, uint8_t round_up,
                       uint64_t* out, uint8_t* error);

#endif
