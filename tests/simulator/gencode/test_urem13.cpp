#include "urem13.h"

int main() {
  uint16_t A[2];
  A[0] = 302;
  A[1] = 3;

  uint16_t res = 345;
  uint16_t expected = 2;

  simulate(A, &res);

  if (res == expected) {
    return 0;
  }

  return 1;
}
