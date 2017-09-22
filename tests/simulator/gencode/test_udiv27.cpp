#include "udiv27.h"

#include <iostream>

using namespace std;

int main() {

  circuit_state state;
  //uint32_t A[2];
  state.self_A[0] = 25;
  state.self_A[1] = 5;

  uint32_t expected = 5;
  //uint32_t res = 30;
  state.self_out = 30;

  //simulate(&res, A);

  simulate(&state);

  // cout << "udiv expected = " << expected << endl;
  // cout << "udiv res      = " << res << endl;

  if (expected == state.self_out) {
    return 0;
  }

  return 1;
}
