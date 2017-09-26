#include "urem13.h"

int main() {
  circuit_state state;
  //uint16_t A[2];
  state.self_A[0] = 302;
  state.self_A[1] = 3;

  state.self_out = 345;

  //  uint16_t res = 345;
  uint16_t expected = 2;

  //simulate(&res, A);
  simulate(&state);

  if (state.self_out == expected) {
    return 0;
  }

  return 1;
}
