#include <cstdio>
#include <stdint.h>

#include "mat2_3_add.h"

int main() {

  circuit_state state;

  // uint64_t A[2][3];
  state.self_A[0][0] = 13;
  state.self_A[0][1] = 2;
  state.self_A[0][2] = 23;
  state.self_A[1][0] = 2;
  state.self_A[1][1] = 2;
  state.self_A[1][2] = 0;

  // uint64_t B[2][3];
  state.self_B[0][0] = 23843;
  state.self_B[0][1] = 2;
  state.self_B[0][2] = 7;
  state.self_B[1][0] = 2;
  state.self_B[1][1] = 90023;
  state.self_B[1][2] = 2;

  // uint64_t C[2][3];
  state.self_out[0][0] = 0;
  state.self_out[0][1] = 0;
  state.self_out[0][2] = 0;
  state.self_out[1][0] = 0;
  state.self_out[1][1] = 0;
  state.self_out[1][2] = 0;

  printf("About to simulate\n");

  // simulate(&C, A, B);

  simulate(&state);

  for (int i = 0; i < 2; i++) {
    for (int j = 0; j < 3; j++) {
      printf("C[%d][%d] = %lu\n", i, j, state.self_out[i][j]);
      uint64_t expected = state.self_A[i][j] + state.self_B[i][j];
      printf("Expected[%d][%d] = %lu\n", i, j, state.self_out[i][j]);
      if (expected != state.self_out[i][j]) { return 1; }
    }
  }

  return 0;
}
