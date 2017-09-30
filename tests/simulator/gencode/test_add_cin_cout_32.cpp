#include "add_cin_cout_32.h"

#include <bitset>
#include <iostream>

using namespace std;

int main() {
  circuit_state state;

  // Creating overfow
  // Set cout from overflow
  state.self_cin = 1;
  state.self_cout = 0;
  state.self_in[0] = 1 << 31;
  state.self_in[1] = 1 << 31;
  state.self_out = 1;

  simulate( &state );

  cout << "cin cout 32 bit out  = " << bitset<32>(state.self_out) << endl;
  cout << "cin cout 32 bit cout = " << bitset<32>(state.self_cout) << endl;
  if (state.self_out != 1) {
    return 1;
  }

  if (state.self_cout != 1) {
    return 1;
  }

  // Overflow without cin
  state.self_cin = 0;
  state.self_cout = 0;
  state.self_in[0] = 1 << 31;
  state.self_in[1] = 1 << 31;
  state.self_out = 1;

  simulate( &state );

  cout << "cin cout 32 bit out  = " << bitset<32>(state.self_out) << endl;
  cout << "cin cout 32 bit cout = " << bitset<32>(state.self_cout) << endl;

  if (state.self_out != 0) {
    return 1;
  }

  if (state.self_cout != 1) {
    return 1;
  }
  

  return 0;
}
