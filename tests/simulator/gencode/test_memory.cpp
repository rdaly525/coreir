#include "memory.h"

#include <iostream>
#include <bitset>

using namespace std;

int main() {
  circuit_state state;
  state.self_clk = 1;
  state.self_clk_last = 0;
  state.self_write_en = 1;
  state.self_read_addr = 1;
  state.self_read_data = 123;
  state.m0[0] = 32;
  state.m0[1] = 5;

  simulate(&state);

  if (state.self_read_data != 5) {
    return 1;
  }

  state.self_write_addr = 1;
  state.self_write_data = 10;

  simulate(&state);

  cout << "Write test" << endl;
  
  if (state.m0[1] != 10) {
    return 1;
  }

  return 0;
}
