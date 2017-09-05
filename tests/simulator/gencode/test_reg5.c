#include "reg5.h"

#include <stdio.h>

int main() {
  uint8_t en = 1;
  uint8_t clk = 1;
  uint8_t clk_last = 0;
  uint8_t r_old = 0;
  uint8_t r_new = 0;
  uint8_t out = 0;
  uint8_t a = (1ULL << 3);

  uint8_t expected = 8;

  for (int i = 1; i < 4; i++) {
    clk = i % 2;

    //simulate(en, &out, a, clk, clk_last, r_old, &r_new);
    simulate(a, clk, clk_last, en, &out, r_old, &r_new);

    printf("New register value = %c\n", r_new);
    
    clk_last = clk;
    r_old = r_new;
  }

  printf("Expected       = %c\n", expected);
  
  if (expected == r_new) {
    return 0;
  } else {
    return 1;
  }
}
