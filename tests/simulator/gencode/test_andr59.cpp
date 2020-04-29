#include "andr59.h"

int main() {
  circuit_state state;
  state.self_A = ((1ULL << 59) - 1);
  state.self_out = 0;

  simulate(&state);

  if (state.self_out != 1) { return 1; }

  state.self_A = 0x011002;

  simulate(&state);

  if (state.self_out != 0) { return 1; }

  return 0;
}
