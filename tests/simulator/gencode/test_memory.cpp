#include "memory.h"

#include <iostream>
#include <bitset>

using namespace std;

int main() {
  circuit_state state;
  state.self_clk = 1;
  state.self_clk_last = 0;
  state.self_write_en = 0;
  state.self_read_addr = 1;
  state.self_read_data = 123;
  state.m0[0] = 32;
  state.m0[1] = 5;

  cout << "state.m0[0] before any test = " << bitset<16>(state.m0[0]) << endl;

  simulate(&state);

  if (state.self_read_data != 5) {
    return 1;
  }

  state.self_write_en = 1;
  state.self_write_addr = 1;
  state.self_write_data = 10;

  simulate(&state);

  cout << "Write test" << endl;
  
  if (state.m0[1] != 10) {
    return 1;
  }

  state.self_write_en = 1;
  state.self_clk_last = 1;
  state.self_write_data = 5;
  state.self_write_addr = 0;

  cout << "state.m0[0] before = " << bitset<16>(state.m0[0]) << endl;

  simulate(&state);

  cout << "state.m0[0] after  = " << bitset<16>(state.m0[0]) << endl;
  
  // If clock and clock last are both high do not update
  if (state.m0[0] != 32) {
    return 1;
  }

  state.self_write_en = 0;
  state.self_clk_last = 0;
  state.self_clk = 1;
  state.self_write_data = 5;
  state.self_write_addr = 0;

  if (state.m0[0] != 32) {
    return 1;
  }
  
  return 0;
}
