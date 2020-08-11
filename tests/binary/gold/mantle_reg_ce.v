module regCE #(
    parameter width = 1
) (
    input [width-1:0] in,
    input ce,
    output [width-1:0] out,
    input clk
);
  reg [width-1:0] value;
  always @(posedge clk) begin
    if (ce) begin
      value <= in;
    end
  end
  assign out = value;
endmodule

module test (
    input [15:0] In0,
    output [15:0] Out0,
    input CLK,
    input CE
);
wire [15:0] Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0$value__CE_out;
regCE #(
    .width(16)
) Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0$value__CE (
    .in(In0),
    .ce(CE),
    .out(Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0$value__CE_out),
    .clk(CLK)
);
assign Out0 = Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0$value__CE_out;
endmodule

