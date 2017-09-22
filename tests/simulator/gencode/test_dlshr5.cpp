#include "dlshr5.h"

#include <bitset>
#include <iostream>

using namespace std;

int main () {
  circuit_state state;
  state.self_A[0] = 1 << 4;
  state.self_A[1] = 3;

  //uint8_t res;

  //simulate(&res, A);

  simulate(&state);

  uint8_t expected = 1 << 1;

  cout << "dlshr5 expected = " << bitset<8>(expected) << endl;
  //cout << "dlshr5 res      = " << bitset<8>(res) << endl;

  if (state.self_out == expected) {
    return 0;
  }

  return 1;
}
