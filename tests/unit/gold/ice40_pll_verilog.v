/* External Modules
module SB_PLL40_CORE (
  input  BYPASS,
  output  PLLOUTCORE,
  output  PLLOUTGLOBAL,
  input  REFERENCECLK,
  input  RESETB
);

endmodule  // SB_PLL40_CORE

*/
module top (
  input  clk,
  input  in,
  output  out,
  output  outClk,
  input  reset
);


  wire  pll__BYPASS;
  wire  pll__PLLOUTCORE;
  wire  pll__PLLOUTGLOBAL;
  wire  pll__REFERENCECLK;
  wire  pll__RESETB;
  SB_PLL40_CORE #(.DIVF(7'h21),.DIVQ(3'h4),.DIVR(4'h0),.FEEDBACK_PATH("SIMPLE"),.FILTER_RANGE(3'h1),.PLLOUT_SELECT("GENCLK")) pll(
    .BYPASS(pll__BYPASS),
    .PLLOUTCORE(pll__PLLOUTCORE),
    .PLLOUTGLOBAL(pll__PLLOUTGLOBAL),
    .REFERENCECLK(pll__REFERENCECLK),
    .RESETB(pll__RESETB)
  );

  assign pll__BYPASS = in;

  assign out = pll__PLLOUTCORE;

  assign outClk = pll__PLLOUTGLOBAL;

  assign pll__REFERENCECLK = clk;

  assign pll__RESETB = reset;


endmodule  // top

