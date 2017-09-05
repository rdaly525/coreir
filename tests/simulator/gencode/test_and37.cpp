#include "and37.h"

#include <cstdio>
#include <stdint.h>

int main() {
  uint64_t one = 1;

  uint64_t ins[2];
  ins[0] = (one << 36) | (one << 37) | (one << 60);
  ins[1] = (one << 36) | (one << 37) | (one << 60);

  uint64_t out;

  simulate(ins, &out);

  // NOTE: This 37th and 60th bits should be masked away by the simulator
  uint64_t expected = one << 36;
  
  printf("and out  = %lu\n", out);
  printf("expected = %lu\n", expected);

  if (expected == out) {
    return 0;
  }

  return 1;
}
