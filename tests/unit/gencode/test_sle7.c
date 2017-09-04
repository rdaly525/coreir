#include "sle7.h"
#include <stdio.h>

int main() {
  uint8_t a[2];
  a[0] = 1 << 6;
  a[1] = 1;

  /* int res = ((int8_t) a[0]) <= ((int8_t) a[1]); */

  /* printf("sle res = %d\n", res); */

  // 1 << 6 is the smallest possible 7 bit 2s complement number
  uint8_t expected = 1;

  uint8_t r = 10;
  simulate(a, &r);

  printf("expected as long = %hhu\n", expected);
  printf("result   as long = %hhu\n", r);
  
  if (expected == r) {
    return 0;
  }

  return 1;
}
