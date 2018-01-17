#include "lbMem.h"

#include <bitset>
#include <iostream>

using namespace std;

void printMem(circuit_state& state) {
  cout << "MEM" << endl;
  for (int i = 0; i < 10; i++) {
    cout << "\tm0$mem[" << i << "] = " << bitset<8>(state.m0$mem[i]) << endl;
  }

}

int main() {
  circuit_state state;
  state.self_clk = 1;
  state.self_clk_last = 0;

  state.self_wdata = 1;
  state.self_wen = 1;

  state.m0$raddr$reg0 = 0;
  state.m0$waddr$reg0 = 0;
  
  for (int i = 0; i < 10; i++) {
    state.m0$mem[i] = 0;
  }

  printMem(state);

  for (int i = 0; i < 9; i++) {
    simulate(&state);

    state.self_clk_last = 0;

    //printMem(state);
    cout << "state.self_rdata " << i << "             = " << bitset<8>(state.self_rdata) << endl;
    //cout << "state.self_m0$raddr$reg0     = " << bitset<8>(state.m0$raddr$reg0) << endl;
    //cout << "state.self_m0$waddr$reg0     = " << bitset<8>(state.m0$waddr$reg0) << endl;

    //cout << "-----------------------------" << endl;
    //cout << "state->m0$raddr$reg0 = " << bitset<8>(state.m0$raddr$reg0) << endl;
  }

  assert(state.self_rdata == 0);

  simulate(&state);

  assert(state.self_rdata == 1);

  simulate(&state);
  simulate(&state);
  simulate(&state);

  assert(state.self_rdata == 1);
  

  return 0;
}
