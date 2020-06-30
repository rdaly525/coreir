#include <cstdio>
#include "neg2.h"

int main() {
  uint8_t a = 1;
  uint8_t res;

  uint8_t expected = 1 << 1;

  circuit_state state;
  state.self_A = 1;
  state.self_res = 23;

  printf("Neg2 before simulating\n");

  // simulate(&res, a);

  simulate(&state);

  // printf("2 bit not expected = %c\n", expected);
  // printf("2 bit not result   = %c\n", res);

  if (state.self_res == expected) { return 0; }

  return 1;
}
