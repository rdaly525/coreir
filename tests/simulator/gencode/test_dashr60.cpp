#include "dashr60.h"

#include <bitset>
#include <iostream>

using namespace std;

int main() {

  circuit_state state;
  state.self_A[0] = 1ULL << 59;
  state.self_A[1] = 3ULL;

  uint64_t expected1 = (1ULL << 59) | (1ULL << 58) | (1ULL << 57) |
    (1ULL << 56);

  state.self_out = 34;

  cout << "About to simulate dashr" << endl;

  simulate(&state);

  cout << "Expected1 = " << std::bitset<64>(expected1) << endl;
  cout << "Result1   = " << std::bitset<64>(state.self_out) << endl;

  if ((expected1 != state.self_out)) { return 1; }

  state.self_A[0] = 1ULL << 58;
  state.self_A[1] = 5ULL;

  uint64_t expected2 = (1ULL << 53);
  state.self_out = 32;

  simulate(&state);

  cout << "Expected2 = " << std::bitset<64>(expected2) << endl;
  cout << "Result2   = " << std::bitset<64>(state.self_out) << endl;

  if ((expected2 != state.self_out)) { return 1; }

  return 0;
}
