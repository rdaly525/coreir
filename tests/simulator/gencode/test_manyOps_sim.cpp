#include "manyOps_sim.h"

#include <cassert>
#include <iostream>

using namespace std;

int main() {
  circuit_state state;

  state.self_clk_last = 0;
  state.self_clk = 1;

  state.reg_0 = 0;
  state.reg_12 = 0;
  state.self_out_12 = 0;

  state.self_in_24 = 1;
  state.self_in_25 = 1;

  simulate(&state);

  cout << "state.reg_12      = " << state.reg_12 << endl;
  cout << "state.self_out_12 = " << state.self_out_12 << endl;

  assert(state.reg_12 == 1);
  assert(state.self_out_12 == 1);
}
