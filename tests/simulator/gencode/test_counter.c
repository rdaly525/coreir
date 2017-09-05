#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "counter.h"

int main() {
  uint8_t self_en = 1;
  //uint16_t* self_out_ptr = malloc(sizeof(uint16_t));
  uint16_t self_out;
  uint8_t self_clk = 0;
  uint8_t self_clk_last = 1;
  uint16_t ri_old_value = 0;

  uint16_t ri_new_value = 0;

  for (int i = 0; i < 20; i++) {
    self_clk = i % 2;
    //simulate(self_en, self_out_ptr, self_clk, self_clk_last, ri_old_value, &ri_new_value);
    simulate(&self_out, ri_old_value, &ri_new_value, self_clk, self_clk_last, self_en);

    // Copy old values to new values
    self_clk_last = self_clk;
    ri_old_value = ri_new_value;
  }

  printf("output = %hu\n", self_out);
  printf("new_register value = %hu\n", ri_new_value);
  
  if ((ri_new_value != 10) || (self_out != 9)) {
    //free(self_out_ptr);

    return 1;
  }
  
  //free(self_out_ptr);

  return 0;
}
