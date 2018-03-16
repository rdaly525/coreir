#include <stdint.h>
#include <cstdio>

#include <iostream>

#include "counter.h"

using namespace std;

int main() {
  uint8_t self_en = 1;
  uint16_t self_out = 0;
  uint8_t self_clk = 0;
  uint8_t self_clk_last = 1;
  uint16_t ri_old_value = 0;

  //uint16_t ri_new_value = 0;

  circuit_state state;
  state.self_en = self_en;
  state.self_clk = self_clk;
  state.self_clk_last = 1;
  state.ri$reg0 = 0;
  //state.ri$reg0_old_value = 0;
  //state.ri$reg0_new_value = 0; //&ri_new_value;
  state.self_out = self_out;

  cout << "Self out initial = " << state.self_out << endl;
  for (int i = 0; i < 20; i++) {

    state.self_clk = i % 2;

    simulate(&state);

    // Copy old values to new values
    state.self_clk_last = state.self_clk;

    printf("output = %hu\n", state.self_out);
    printf("new_register value = %hu\n", state.ri$reg0); //_new_value);
    
  }

  printf("output = %hu\n", state.self_out);
  printf("new_register value = %hu\n", state.ri$reg0); //_new_value);
  
  //if ((state.ri$reg0_new_value != 10) || (state.self_out != 9)) {
  if ((state.ri$reg0 != 10) || (state.self_out != 10)) {
    return 1;
  }
  

  return 0;
}
