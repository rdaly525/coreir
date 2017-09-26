#include "sle7.h"

#include <cstdio>

int main() {

  circuit_state state;
  state.self_A[0] = 1 << 6;
  state.self_A[1] = 1;

  state.self_out = 12;

  // uint8_t a[2];
  // a[0] = 1 << 6;
  // a[1] = 1;

  /* int res = ((int8_t) a[0]) <= ((int8_t) a[1]); */

  /* printf("sle res = %d\n", res); */

  // 1 << 6 is the smallest possible 7 bit 2s complement number
  uint8_t expected = 1;

  printf("expected as long before calling simulate = %hhu\n", expected);

  simulate(&state);
  //uint8_t r = 10;
  //simulate(&r, a);

  printf("expected as long = %hhu\n", expected);
  printf("result   as long = %hhu\n", state.self_out);
  
  if (expected == state.self_out) {
    return 0;
  }

  return 1;
}
