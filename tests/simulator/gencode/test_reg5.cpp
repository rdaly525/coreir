#include "reg5.h"

#include <cstdio>

int main() {
  uint8_t en = 1;
  uint8_t clk = 1;
  uint8_t clk_last = 0;
  uint8_t r_old = 0;
  uint8_t r_new = 0;
  uint8_t out = 0;
  uint8_t a = (1ULL << 3);

  uint8_t expected = 8;

  circuit_state state;
  state.self_en = en;
  state.self_a = a;
  state.self_clk = clk;
  state.self_clk_last = clk_last;
  state.r$reg0 = r_old;

  for (int i = 1; i < 4; i++) {
    state.self_clk = i % 2;

    simulate(&state);

    printf("New register value = %c\n", state.r$reg0);

    state.self_clk_last = state.self_clk;
  }

  printf("Expected       = %c\n", expected);

  if (expected == state.r$reg0) { return 0; }
  else {
    return 1;
  }
}
