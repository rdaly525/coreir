#include "dshl32.h"

int main() {
  uint32_t A[2];
  A[0] = 1 << 2;
  A[1] = 3;

  uint32_t res = 0;
  uint32_t expected = (1 << 2) << 3;

  simulate(A, &res);

  if (res == expected) {
    return 0;
  }

  return 1;
}
