module coreir_reg #(
    parameter width = 1,
    parameter clk_posedge = 1,
    parameter init = 1
) (
    input clk,
    input [width-1:0] in,
    output [width-1:0] out
);
  reg [width-1:0] outReg=init;
  wire real_clk;
  assign real_clk = clk_posedge ? clk : ~clk;
  always @(posedge real_clk) begin
    outReg <= in;
  end
  assign out = outReg;
endmodule

module corebit_term (
    input in
);

endmodule

module Register (
    input [3:0] I,
    output [3:0] O,
    input CLK
);
coreir_reg #(
    .clk_posedge(1'b1),
    .init(4'h0),
    .width(4)
) reg_P_inst0 (
    .clk(CLK),
    .in(I),
    .out(O)
);
endmodule

module Mux2xUInt2 (
    input [1:0] I0,
    input [1:0] I1,
    input S,
    output [1:0] O
);
reg [1:0] coreir_commonlib_mux2x2_inst0_out;
always @(*) begin
if (S == 0) begin
    coreir_commonlib_mux2x2_inst0_out = I0;
end else begin
    coreir_commonlib_mux2x2_inst0_out = I1;
end
end

assign O = coreir_commonlib_mux2x2_inst0_out;
endmodule

module Register_unq1 (
    input [1:0] I,
    output [1:0] O,
    input CE,
    input CLK
);
wire [1:0] enable_mux_O;
Mux2xUInt2 enable_mux (
    .I0(O),
    .I1(I),
    .S(CE),
    .O(enable_mux_O)
);
coreir_reg #(
    .clk_posedge(1'b1),
    .init(2'h0),
    .width(2)
) reg_P_inst0 (
    .clk(CLK),
    .in(enable_mux_O),
    .out(O)
);
endmodule

module ASSERT_ON_compile_guard (
    input port_0,
    input CLK,
    input [3:0] port_1
);
wire [1:0] Register_inst0_O;
wire _magma_inline_wire0;
wire [1:0] magma_Bits_2_add_inst0_out;
Register_unq1 Register_inst0 (
    .I(magma_Bits_2_add_inst0_out),
    .O(Register_inst0_O),
    .CE(port_0),
    .CLK(CLK)
);
assign _magma_inline_wire0 = (~ (Register_inst0_O == 2'h3)) | (port_1 == 4'h3);
assign magma_Bits_2_add_inst0_out = 2'(Register_inst0_O + 2'h1);
initial assert (_magma_inline_wire0);
endmodule

module _Top (
    input CLK,
    input [3:0] I_data,
    input I_valid,
    output [3:0] O
);
`ifdef ASSERT_ON
ASSERT_ON_compile_guard ASSERT_ON_compile_guard (
    .port_0(I_valid),
    .CLK(CLK),
    .port_1(O)
);
`endif
Register Register_inst0 (
    .I(I_data),
    .O(O),
    .CLK(CLK)
);
endmodule

