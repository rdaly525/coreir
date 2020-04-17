// Module `SB_PLL40_CORE` defined externally
module top (
    input clk,
    input reset,
    input in,
    output out,
    output outClk
);
wire pll_PLLOUTCORE;
wire pll_PLLOUTGLOBAL;
SB_PLL40_CORE #(
    .DIVF(7'h21),
    .DIVQ(3'h4),
    .DIVR(4'h0),
    .FEEDBACK_PATH("SIMPLE"),
    .FILTER_RANGE(3'h1),
    .PLLOUT_SELECT("GENCLK")
) pll (
    .BYPASS(in),
    .PLLOUTCORE(pll_PLLOUTCORE),
    .PLLOUTGLOBAL(pll_PLLOUTGLOBAL),
    .REFERENCECLK(clk),
    .RESETB(reset)
);
assign out = pll_PLLOUTCORE;
assign outClk = pll_PLLOUTGLOBAL;
endmodule

