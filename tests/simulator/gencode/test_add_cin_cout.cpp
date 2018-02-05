#include "add_cin_cout.h"

int main() {

  circuit_state state;

  // Set cout from overflow
  state.self_cin = 0;
  state.self_cout = 0;
  state.self_in[0] = 1 << 30;
  state.self_in[1] = 1 << 30;
  state.self_out = 1;

  simulate( &state );

  if (state.self_out != 0) {
    return 1;
  }

  if (state.self_cout != 1) {
    return 1;
  }
  
  

  return 0;

}
