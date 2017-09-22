#include "sdiv5.h"

#include <iostream>
#include <bitset>

using namespace std;

int main() {
  circuit_state state;
  //  uint8_t A[2];
  state.self_A[0] = (1 << 4) + 1;
  state.self_A[1] = 2;

  // -15 / 2 == -7
  uint8_t expected = 0b11001;

  //uint8_t res = 234;
  state.self_out = 234;

  //simulate(&res, A);

  simulate(&state);

  cout << "sdiv expected = " << bitset<8>(expected) << endl;
  //cout << "sdiv res      = " << bitset<8>(res) << endl;

  if (expected == state.self_out) {
    return 0;
  }

  return 1;
}
