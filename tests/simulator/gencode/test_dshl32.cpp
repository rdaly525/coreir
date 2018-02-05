#include "dshl32.h"

int main() {

  circuit_state state;
  state.self_A[0] = 1 << 2;
  state.self_A[1] = 3;

  // uint32_t A[2];
  // A[0] = 1 << 2;
  // A[1] = 3;

  //uint32_t res = 0;
  uint32_t expected = (1 << 2) << 3;

  //simulate(&res, A);

  simulate(&state);

  if (state.self_out == expected) {
    return 0;
  }

  return 1;
}
