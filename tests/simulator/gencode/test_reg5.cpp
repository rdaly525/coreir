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
  //state.r_old_value = r_old;
  //state.r_new_value = 0; //&r_new;
  state.r = r_old;

  for (int i = 1; i < 4; i++) {
    state.self_clk = i % 2;

    //simulate(en, &out, a, clk, clk_last, r_old, &r_new);
    //simulate(&r_new, &out, r_old, a, clk, clk_last, en); //, &r_new);

    simulate(&state);

    //printf("New register value = %c\n", state.r_new_value); //r_new);
    printf("New register value = %c\n", state.r);
    
    state.self_clk_last = state.self_clk;
    //state.r_old_value = state.r_new_value;
  }

  printf("Expected       = %c\n", expected);
  
  //if (expected == state.r_new_value) {
  if (expected == state.r) {
    return 0;
  } else {
    return 1;
  }
}
