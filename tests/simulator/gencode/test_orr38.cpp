#include "orr38.h"

int main() {
  circuit_state state;
  state.self_A = 0b100010111;
  state.self_out = 0;

  simulate(&state);

  if (state.self_out != 1) { return 1; }

  state.self_A = 0;

  simulate(&state);

  if (state.self_out != 0) { return 1; }

  return 0;
}
