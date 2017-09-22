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

  circuit_state state;
  state.self_en = self_en;
  state.self_clk = self_clk;
  state.self_clk_last = self_clk_last;
  state.ri_old_value = ri_old_value;
  state.ri_new_value = &ri_new_value;
  state.self_out = self_out;
  
  //simulate(&ri_new_value, &self_out, ri_old_value, self_clk, self_clk_last, self_en);
  simulate(&state);

  printf("output = %hu\n", state.self_out);
  printf("new_register value = %hu\n", ri_new_value);
  
  if ((*(state.ri_new_value) != 5) || (state.self_out != 5)) {
    return 1;
  }

  state.self_clk = 1;
  state.self_en = 0;
  simulate(&state);

  //simulate(&ri_new_value, &self_out, ri_old_value, self_clk, self_clk_last, self_en);

  printf("output = %hu\n", self_out);
  printf("new_register value = %hu\n", ri_new_value);

  if ((*(state.ri_new_value) != 5) || (state.self_out != 5)) {
    return 1;
  }
  
  return 0;
}
