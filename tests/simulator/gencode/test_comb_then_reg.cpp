#include "comb_then_reg.h"

#include <cassert>
#include <iostream>
#include <bitset>

using namespace std;

int main() {
  circuit_state state;
  state.reg0 = 0;
  state.self_clk = 1;
  state.self_clk_last = 0;
  state.self_in_0 = 1;
  state.self_in_1 = 1;

  simulate(&state);

  cout << "After first high clock" << endl;
  cout << "state.self_out_0 = " << bitset<8>(state.self_out_0) << endl;
  cout << "state.self_out_1 = " << bitset<8>(state.self_out_1) << endl;

  assert(state.self_out_0 == 2);
  assert(state.self_out_1 == 2);

  simulate(&state);

  assert(state.self_out_0 == 2);
  assert(state.self_out_1 == 2);
  
  cout << "After second high clock" << endl;
  cout << "state.self_out_0 = " << bitset<8>(state.self_out_0) << endl;
  cout << "state.self_out_1 = " << bitset<8>(state.self_out_1) << endl;

  state.self_in_0 = 0;
  state.self_clk = 0;
  state.self_clk_last = 1;

  simulate(&state);

  assert(state.self_out_0 == 1);
  assert(state.self_out_1 == 2);
  
  cout << "After falling clock edge" << endl;
  cout << "state.self_out_0 = " << bitset<8>(state.self_out_0) << endl;
  cout << "state.self_out_1 = " << bitset<8>(state.self_out_1) << endl;
  
  return 0;
}
