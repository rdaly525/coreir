#include "srem4.h"

#include <bitset>
#include <iostream>

using namespace std;

int main() {

  circuit_state state;
  state.self_in[0] = 27;
  state.self_in[1] = 14;
  state.self_in[2] = 1 | (1 << 4) | (1 << 5);

  state.self_out = 234;

  // uint8_t A[3];
  // A[0] = 27;
  // A[1] = 14;
  // // -15 in 6 bit signed
  // A[2] = 1 | (1 << 4) | (1 << 5);

  // -1
  uint8_t expected = 0b1;

  // uint8_t res = 234;

  cout << "3 srem before       = " << bitset<8>(expected) << endl;
  cout << "3 srem before       = " << bitset<8>(state.self_out) << endl;

  cout << "A0 srem before      = " << bitset<8>(state.self_in[0]) << endl;
  cout << "A1 srem before      = " << bitset<8>(state.self_in[1]) << endl;
  cout << "A2 srem before      = " << bitset<8>(state.self_in[2]) << endl;

  // simulate(&res, A);

  simulate(&state);

  cout << "3 srem expected = " << bitset<8>(expected) << endl;
  cout << "3 srem res      = " << bitset<8>(state.self_out) << endl;

  if (expected == state.self_out) { return 0; }

  return 1;
}
