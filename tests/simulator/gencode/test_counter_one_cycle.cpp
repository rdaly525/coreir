#include <cstdio>
#include <stdint.h>

#include "counter.h"

int main() {
  uint8_t self_en = 1;
  uint16_t self_out = 5;
  uint8_t self_clk = 0;
  uint8_t self_clk_last = 0;

  circuit_state state;
  state.self_en = self_en;
  state.self_clk = self_clk;
  state.self_clk_last = self_clk_last;
  state.ri$reg0 = 5;
  state.self_out = self_out;

  simulate(&state);

  printf("output = %hu\n", state.self_out);
  printf("new_register value = %hu\n", state.ri$reg0);

  if ((state.ri$reg0 != 5) || (state.self_out != 5)) { return 1; }

  state.self_clk = 1;
  state.self_en = 0;
  simulate(&state);

  printf("output = %hu\n", self_out);

  printf("new_register value = %hu\n", state.ri$reg0);

  if ((state.ri$reg0 != 5) || (state.self_out != 5)) { return 1; }

  return 0;
}
