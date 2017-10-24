#include "add4_parallel.h"

int main() {
  circuit_state state;
  state.self_in0 = 1;
  state.self_in1 = 2;
  state.self_in2 = 5;
  state.self_in3 = 3;

  state.add1_out = 0;
  state.self_out = 0;

  uint32_t expected = 1 + 2 + 5 + 3;

  simulate( &state );

  if (state.self_out != expected) {
    return 1;
  }

  return 0;
}
