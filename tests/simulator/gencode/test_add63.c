#include "add63.h"

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main() {
  uint64_t one = 1;

  uint64_t ins[2];
  ins[0] = (one << 62);
  ins[1] = (one << 62);

  uint64_t out;

  simulate(ins, &out);

  // NOTE: 37th and 60th bits should be masked away by the simulator
  uint64_t expected = 0;
  
  printf("and out  = %lu\n", out);
  printf("expected = %lu\n", expected);

  if (expected == out) {
    return 0;
  }

  return 1;
}

