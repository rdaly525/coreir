#include "mux8.h"

int main() {

  uint8_t A[2];
  A[0] = 34;
  A[1] = 12;

  uint8_t out_0 = 5;
  uint8_t out_1 = 2;

  uint8_t sel_0 = 0;
  uint8_t sel_1 = 1;

  simulate(&out_0, A, sel_0);
  simulate(&out_1, A, sel_1);


  printf("out_0 = %hhu\n", out_0);
  printf("out_1 = %hhu\n", out_1);

  if ((out_0 == A[0]) && (out_1 == A[1])) {
    return 0;
  }

  return 1;
}
