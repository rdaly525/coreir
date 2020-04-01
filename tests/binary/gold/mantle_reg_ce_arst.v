module regCE_arst #(
    parameter width = 1,
    parameter init = 1
) (
    input [width-1:0] in,
    input ce,
    output [width-1:0] out,
    input clk,
    input arst
);
  reg [width-1:0] value;
  always @(posedge clk, posedge arst) begin
    if (arst) begin
      value <= init;
    end
    else if (ce) begin
      value <= in;
    end
  end
  assign out = value;
endmodule

module test (
    input [15:0] In0,
    output [15:0] Out0,
    input CLK,
    input CE,
    input ASYNCRESET
);
wire [15:0] Register_has_ce_True_has_reset_False_has_async_reset_True_has_async_resetn_False_type_Bits_n_16_inst0$value__CE_out;
regCE_arst #(
    .init(16'h0000),
    .width(16)
) Register_has_ce_True_has_reset_False_has_async_reset_True_has_async_resetn_False_type_Bits_n_16_inst0$value__CE (
    .in(In0),
    .ce(CE),
    .out(Register_has_ce_True_has_reset_False_has_async_reset_True_has_async_resetn_False_type_Bits_n_16_inst0$value__CE_out),
    .clk(CLK),
    .arst(ASYNCRESET)
);
assign Out0 = Register_has_ce_True_has_reset_False_has_async_reset_True_has_async_resetn_False_type_Bits_n_16_inst0$value__CE_out;
endmodule

