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

module Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16 (
    input [15:0] I,
    output [15:0] O,
    input CLK,
    input CE
);
wire [15:0] value__CE_out;
regCE #(
    .width(16)
) value__CE (
    .in(I),
    .ce(CE),
    .out(value__CE_out),
    .clk(CLK)
);
assign O = value__CE_out;
endmodule

module test (
    input [15:0] In0,
    output [15:0] Out0,
    input CLK,
    input CE
);
wire [15:0] Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0_O;
Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16 Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0 (
    .I(In0),
    .O(Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0_O),
    .CLK(CLK),
    .CE(CE)
);
assign Out0 = Register_has_ce_True_has_reset_False_has_async_reset_False_has_async_resetn_False_type_Bits_n_16_inst0_O;
endmodule

