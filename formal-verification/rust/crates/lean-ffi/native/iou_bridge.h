#ifndef IOU_BRIDGE_H
#define IOU_BRIDGE_H

#include <stdint.h>

typedef struct {
  int64_t mantissa;
  int64_t exponent;
} lean_bridge_iou;

typedef struct {
  uint8_t negative;
  uint64_t mantissa;
  int64_t exponent;
} lean_bridge_number;

void lean_iou_build_accessors(int64_t mantissa, int64_t exponent, lean_bridge_iou* out);
int lean_iou_from_number_bridge(lean_bridge_number value, uint8_t mode, lean_bridge_iou* out, uint8_t* error);
int lean_iou_of_mantissa_exp_bridge(int64_t mantissa, int64_t exponent, uint8_t mode, lean_bridge_iou* out, uint8_t* error);
int lean_iou_of_number_bridge(lean_bridge_number value, uint8_t mode, lean_bridge_iou* out, uint8_t* error);
int lean_iou_to_number_bridge(lean_bridge_iou value, uint8_t mode, lean_bridge_number* out, uint8_t* error);
uint8_t lean_iou_compare_bridge(uint8_t relation, lean_bridge_iou left, lean_bridge_iou right, uint8_t mode, uint8_t* error);
int lean_iou_unary_bridge(uint8_t op, lean_bridge_iou value, uint8_t mode, lean_bridge_iou* out, uint8_t* error);
int lean_iou_binary_bridge(uint8_t op, lean_bridge_iou left, lean_bridge_iou right, uint8_t mode, lean_bridge_iou* out, uint8_t* error);
int lean_iou_mul_ratio_bridge(lean_bridge_iou value, uint32_t num, uint32_t den, uint8_t round_up, uint8_t mode, lean_bridge_iou* out, uint8_t* error);

#endif
