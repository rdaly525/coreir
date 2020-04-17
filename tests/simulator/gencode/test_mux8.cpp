#include "mux8.h"

int main() {

  circuit_state state;

  // uint8_t A[2];
  state.self_A[0] = 34;
  state.self_A[1] = 12;

  state.self_out = 5;
  state.self_sel = 0;
  // uint8_t out_0 = 5;

  // uint8_t sel_0 = 0;

  simulate(&state);

  if ((state.self_out != state.self_A[0])) { return 1; }

  state.self_sel = 1;

  simulate(&state);

  // simulate(&out_0, A, sel_0);

  // uint8_t sel_1 = 1;
  // uint8_t out_1 = 2;
  // simulate(&out_1, A, sel_1);

  // printf("out_0 = %hhu\n", out_0);
  // printf("out_1 = %hhu\n", out_1);

  if ((state.self_out != state.self_A[1])) { return 1; }

  return 0;
}
