#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
void simulate( uint16_t (*self_out_ptr), uint16_t ri_old_value, uint16_t* ri_new_value, uint8_t  self_clk, uint8_t  self_clk_last, uint8_t  self_en );