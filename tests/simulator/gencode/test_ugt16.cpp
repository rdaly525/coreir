#include "ugt16.h"

int main() {
  circuit_state state;
  state.self_A[0] = 1 << 15;
  state.self_A[1] = (1 << 15) | 1;
  state.self_out = 12;

  simulate(&state);

  // In this example self_A[0] < self_A[1] so (self_A[0] > self_A[1]) == 0
  if (state.self_out != 0) {
    return 1;
  }

  return 0;
}
