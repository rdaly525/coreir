#include "fanout_2_reg.h"

#include <cassert>

int main() {
  circuit_state s;
  s.self_in = 4;
  s.self_clk = 1;
  s.self_clk_last = 0;

  simulate(&s);

  assert(s.self_out_0 == 4);
  assert(s.self_out_1 == 4);
}
