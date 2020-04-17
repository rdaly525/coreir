#include "multiply_shift_16.h"

#include <bitset>
#include <iostream>

using namespace std;

int main() {
  circuit_state state;
  state.self_A[0] = 288;
  state.self_A[1] = 288;

  simulate(&state);

  cout << "state.self_out = " << bitset<16>(state.self_out) << endl;
  assert(state.self_out == 0b0000010001000000);

  state.self_A[0] = 1 << 14;
  state.self_A[1] = 1 << 1;

  simulate(&state);

  cout << "state.self_out = " << bitset<16>(state.self_out) << endl;
  assert(state.self_out == 0b1111100000000000);

  return 0;
}
