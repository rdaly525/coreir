#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
void simulate( uint8_t  self_a, uint8_t  self_clk, uint8_t  self_clk_last, uint8_t  self_en, uint8_t (*self_out_ptr), uint8_t r_old_value, uint8_t* r_new_value );