module top (input clk, input in, output out, output outClk, input reset);
SB_PLL40_CORE #(.DIVF(7'h21), .DIVQ(3'h4), .DIVR(4'h0), .FEEDBACK_PATH("SIMPLE"), .FILTER_RANGE(3'h1), .PLLOUT_SELECT("GENCLK")) pll(.BYPASS(in), .PLLOUTCORE(out), .PLLOUTGLOBAL(outClk), .REFERENCECLK(clk), .RESETB(reset));
endmodule

