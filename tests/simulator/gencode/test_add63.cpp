#include "add63.h"

#include <cstdio>
#include <stdint.h>

int main() {
  uint64_t one = 1;

  circuit_state state;
  state.self_input[0] = one << 62;
  state.self_input[1] = one << 62;

  // uint64_t ins[2];
  // ins[0] = (one << 62);
  // ins[1] = (one << 62);

  // uint64_t out;

  // simulate(ins, &out);

  simulate(&state);

  // NOTE: 37th and 60th bits should be masked away by the simulator
  uint64_t expected = 0;

  // printf("and out  = %lu\n", out);
  // printf("expected = %lu\n", expected);

  if (expected == state.self_output) { return 0; }

  return 1;
}
