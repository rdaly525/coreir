#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "mat2_3_add.h"

int main() {
  /* uint64_t** A = (uint64_t**) malloc(sizeof(uint64_t)*6); */
  /* uint64_t** B = (uint64_t**) malloc(sizeof(uint64_t)*6); */
  /* uint64_t** C = (uint64_t**) malloc(sizeof(uint64_t)*6); */

  uint64_t A[2][3];
  A[0][0] = 13;
  A[0][1] = 2;
  A[0][2] = 23;
  A[1][0] = 2;
  A[1][1] = 2;
  A[1][2] = 0;
  
  uint64_t B[2][3];
  B[0][0] = 23843;
  B[0][1] = 2;
  B[0][2] = 7;
  B[1][0] = 2;
  B[1][1] = 90023;
  B[1][2] = 2;


  uint64_t C[2][3];
  C[0][0] = 0;
  C[0][1] = 0;
  C[0][2] = 0;
  C[1][0] = 0;
  C[1][1] = 0;
  C[1][2] = 0;

  printf("About to simulate\n");

  simulate(A, B, &C);

  for (int i = 0; i < 2; i++) {
    for (int j = 0; j < 3; j++) {
      printf("C[%d][%d] = %llu\n", i, j, C[i][j]);
      uint64_t expected = A[i][j] + B[i][j];
      printf("Expected[%d][%d] = %llu\n", i, j, C[i][j]);      
      if (expected != C[i][j]) {
	return 1;
      }
    }
  }

  return 0;

}
