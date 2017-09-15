#include <stdint.h>
#include <cstdio>

#include "counter.h"

int main() {
  uint8_t self_en = 1;
  uint16_t self_out;
  uint8_t self_clk = 0;
  uint8_t self_clk_last = 0;
  uint16_t ri_old_value = 5;

  uint16_t ri_new_value = 1;

  simulate(&ri_new_value, &self_out, ri_old_value, self_clk, self_clk_last, self_en);

  printf("output = %hu\n", self_out);
  printf("new_register value = %hu\n", ri_new_value);
  
  if ((ri_new_value != 5) || (self_out != 5)) {
    return 1;
  }

  self_clk = 1;
  self_en = 0;
  simulate(&ri_new_value, &self_out, ri_old_value, self_clk, self_clk_last, self_en);

  printf("output = %hu\n", self_out);
  printf("new_register value = %hu\n", ri_new_value);

  if ((ri_new_value != 5) || (self_out != 5)) {
    return 1;
  }
  
  return 0;
}
