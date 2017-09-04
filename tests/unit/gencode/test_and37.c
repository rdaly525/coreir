#include "and37.h"

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main() {
  uint64_t one = 1;

  uint64_t ins[2];
  ins[0] = (one << 36) | (one << 37) | (one << 60);
  ins[1] = (one << 36) | (one << 37) | (one << 60);

  uint64_t out;

  simulate(ins, &out);

  // NOTE: This 37th and 60th bits should be masked away by the simulator
  uint64_t expected = one << 36;
  
  printf("and out  = %llu\n", out);
  printf("expected = %llu\n", expected);

  if (expected == out) {
    return 0;
  }

  return 1;
}
