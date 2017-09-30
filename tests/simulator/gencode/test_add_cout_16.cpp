#include "add_cout_16.h"

#include <iostream>
#include <bitset>

using namespace std;

int main() {
  circuit_state state;
  state.self_cout = 0;
  state.self_in[0] = (1 << 15) | 1;
  state.self_in[1] = (1 << 15) | (1 << 14);

  simulate(&state);

  cout << "self_cout = " << bitset<16>(state.self_cout) << endl;
  cout << "self_out  = " << bitset<16>(state.self_out) << endl;

  if (state.self_out != ((1 << 14) | 1)) {
    return 1;
  }

  if (state.self_cout != 1) {
    return 1;
  }

  return 0;
}
