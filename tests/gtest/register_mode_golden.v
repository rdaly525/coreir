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

module Mux2xOutBits4 (
    input [3:0] I0,
    input [3:0] I1,
    input S,
    output [3:0] O
);
reg [3:0] coreir_commonlib_mux2x4_inst0_out;
always @(*) begin
if (S == 0) begin
    coreir_commonlib_mux2x4_inst0_out = I0;
end else begin
    coreir_commonlib_mux2x4_inst0_out = I1;
end
end

assign O = coreir_commonlib_mux2x4_inst0_out;
endmodule

module Register_comb (
    input [3:0] value,
    input en,
    input [3:0] self_value_O,
    output [3:0] O0,
    output [3:0] O1
);
Mux2xOutBits4 Mux2xOutBits4_inst0 (
    .I0(self_value_O),
    .I1(value),
    .S(en),
    .O(O0)
);
assign O1 = self_value_O;
endmodule

module Register (
    input [3:0] value,
    input en,
    input CLK,
    output [3:0] O
);
wire [3:0] Register_comb_inst0_O0;
wire [3:0] reg_P_inst0_out;
Register_comb Register_comb_inst0 (
    .value(value),
    .en(en),
    .self_value_O(reg_P_inst0_out),
    .O0(Register_comb_inst0_O0),
    .O1(O)
);
coreir_reg #(
    .clk_posedge(1'b1),
    .init(4'h0),
    .width(4)
) reg_P_inst0 (
    .clk(CLK),
    .in(Register_comb_inst0_O0),
    .out(reg_P_inst0_out)
);
endmodule

module Mux2xOutBit (
    input I0,
    input I1,
    input S,
    output O
);
reg [0:0] coreir_commonlib_mux2x1_inst0_out;
always @(*) begin
if (S == 0) begin
    coreir_commonlib_mux2x1_inst0_out = I0;
end else begin
    coreir_commonlib_mux2x1_inst0_out = I1;
end
end

assign O = coreir_commonlib_mux2x1_inst0_out[0];
endmodule

module RegisterMode_comb (
    input [1:0] mode,
    input [3:0] const_,
    input [3:0] value,
    input clk_en,
    input config_we,
    input [3:0] config_data,
    input [3:0] self_register_O,
    output [3:0] O0,
    output O1,
    output [3:0] O2,
    output [3:0] O3
);
wire Mux2xOutBit_inst0_O;
wire Mux2xOutBit_inst1_O;
wire Mux2xOutBit_inst2_O;
wire Mux2xOutBit_inst3_O;
wire Mux2xOutBit_inst4_O;
wire [3:0] Mux2xOutBits4_inst0_O;
wire [3:0] Mux2xOutBits4_inst1_O;
wire [3:0] Mux2xOutBits4_inst10_O;
wire [3:0] Mux2xOutBits4_inst11_O;
wire [3:0] Mux2xOutBits4_inst2_O;
wire [3:0] Mux2xOutBits4_inst3_O;
wire [3:0] Mux2xOutBits4_inst4_O;
wire [3:0] Mux2xOutBits4_inst5_O;
wire [3:0] Mux2xOutBits4_inst6_O;
wire [3:0] Mux2xOutBits4_inst7_O;
wire [3:0] Mux2xOutBits4_inst8_O;
wire [3:0] Mux2xOutBits4_inst9_O;
wire magma_Bit_not_inst0_out;
wire magma_Bit_not_inst1_out;
wire magma_Bit_not_inst2_out;
wire magma_Bit_not_inst3_out;
wire magma_Bit_not_inst4_out;
wire magma_Bit_not_inst5_out;
wire magma_Bit_not_inst6_out;
wire magma_Bits_2_eq_inst0_out;
wire magma_Bits_2_eq_inst1_out;
wire magma_Bits_2_eq_inst10_out;
wire magma_Bits_2_eq_inst11_out;
wire magma_Bits_2_eq_inst12_out;
wire magma_Bits_2_eq_inst13_out;
wire magma_Bits_2_eq_inst2_out;
wire magma_Bits_2_eq_inst3_out;
wire magma_Bits_2_eq_inst4_out;
wire magma_Bits_2_eq_inst5_out;
wire magma_Bits_2_eq_inst6_out;
wire magma_Bits_2_eq_inst7_out;
wire magma_Bits_2_eq_inst8_out;
wire magma_Bits_2_eq_inst9_out;
Mux2xOutBit Mux2xOutBit_inst0 (
    .I0(clk_en),
    .I1(1'b0),
    .S(magma_Bits_2_eq_inst1_out),
    .O(Mux2xOutBit_inst0_O)
);
Mux2xOutBit Mux2xOutBit_inst1 (
    .I0(Mux2xOutBit_inst0_O),
    .I1(1'b0),
    .S(magma_Bits_2_eq_inst4_out),
    .O(Mux2xOutBit_inst1_O)
);
Mux2xOutBit Mux2xOutBit_inst2 (
    .I0(Mux2xOutBit_inst1_O),
    .I1(1'b1),
    .S(magma_Bit_not_inst1_out),
    .O(Mux2xOutBit_inst2_O)
);
Mux2xOutBit Mux2xOutBit_inst3 (
    .I0(clk_en),
    .I1(1'b0),
    .S(magma_Bits_2_eq_inst7_out),
    .O(Mux2xOutBit_inst3_O)
);
Mux2xOutBit Mux2xOutBit_inst4 (
    .I0(Mux2xOutBit_inst3_O),
    .I1(1'b0),
    .S(magma_Bits_2_eq_inst11_out),
    .O(Mux2xOutBit_inst4_O)
);
Mux2xOutBit Mux2xOutBit_inst5 (
    .I0(Mux2xOutBit_inst4_O),
    .I1(1'b1),
    .S(magma_Bit_not_inst4_out),
    .O(O1)
);
Mux2xOutBits4 Mux2xOutBits4_inst0 (
    .I0(value),
    .I1(value),
    .S(magma_Bits_2_eq_inst0_out),
    .O(Mux2xOutBits4_inst0_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst1 (
    .I0(self_register_O),
    .I1(self_register_O),
    .S(magma_Bits_2_eq_inst2_out),
    .O(Mux2xOutBits4_inst1_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst10 (
    .I0(Mux2xOutBits4_inst7_O),
    .I1(const_),
    .S(magma_Bits_2_eq_inst12_out),
    .O(Mux2xOutBits4_inst10_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst11 (
    .I0(Mux2xOutBits4_inst8_O),
    .I1(self_register_O),
    .S(magma_Bits_2_eq_inst13_out),
    .O(Mux2xOutBits4_inst11_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst12 (
    .I0(Mux2xOutBits4_inst9_O),
    .I1(config_data),
    .S(magma_Bit_not_inst3_out),
    .O(O0)
);
Mux2xOutBits4 Mux2xOutBits4_inst13 (
    .I0(Mux2xOutBits4_inst10_O),
    .I1(self_register_O),
    .S(magma_Bit_not_inst5_out),
    .O(O2)
);
Mux2xOutBits4 Mux2xOutBits4_inst14 (
    .I0(Mux2xOutBits4_inst11_O),
    .I1(self_register_O),
    .S(magma_Bit_not_inst6_out),
    .O(O3)
);
Mux2xOutBits4 Mux2xOutBits4_inst2 (
    .I0(Mux2xOutBits4_inst0_O),
    .I1(value),
    .S(magma_Bits_2_eq_inst3_out),
    .O(Mux2xOutBits4_inst2_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst3 (
    .I0(Mux2xOutBits4_inst1_O),
    .I1(self_register_O),
    .S(magma_Bits_2_eq_inst5_out),
    .O(Mux2xOutBits4_inst3_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst4 (
    .I0(Mux2xOutBits4_inst2_O),
    .I1(config_data),
    .S(magma_Bit_not_inst0_out),
    .O(Mux2xOutBits4_inst4_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst5 (
    .I0(Mux2xOutBits4_inst3_O),
    .I1(self_register_O),
    .S(magma_Bit_not_inst2_out),
    .O(Mux2xOutBits4_inst5_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst6 (
    .I0(value),
    .I1(value),
    .S(magma_Bits_2_eq_inst6_out),
    .O(Mux2xOutBits4_inst6_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst7 (
    .I0(self_register_O),
    .I1(value),
    .S(magma_Bits_2_eq_inst8_out),
    .O(Mux2xOutBits4_inst7_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst8 (
    .I0(self_register_O),
    .I1(self_register_O),
    .S(magma_Bits_2_eq_inst9_out),
    .O(Mux2xOutBits4_inst8_O)
);
Mux2xOutBits4 Mux2xOutBits4_inst9 (
    .I0(Mux2xOutBits4_inst6_O),
    .I1(value),
    .S(magma_Bits_2_eq_inst10_out),
    .O(Mux2xOutBits4_inst9_O)
);
assign magma_Bit_not_inst0_out = ~ (config_we ^ 1'b1);
assign magma_Bit_not_inst1_out = ~ (config_we ^ 1'b1);
assign magma_Bit_not_inst2_out = ~ (config_we ^ 1'b1);
assign magma_Bit_not_inst3_out = ~ (config_we ^ 1'b1);
assign magma_Bit_not_inst4_out = ~ (config_we ^ 1'b1);
assign magma_Bit_not_inst5_out = ~ (config_we ^ 1'b1);
assign magma_Bit_not_inst6_out = ~ (config_we ^ 1'b1);
assign magma_Bits_2_eq_inst0_out = mode == 2'h1;
assign magma_Bits_2_eq_inst1_out = mode == 2'h1;
assign magma_Bits_2_eq_inst10_out = mode == 2'h0;
assign magma_Bits_2_eq_inst11_out = mode == 2'h0;
assign magma_Bits_2_eq_inst12_out = mode == 2'h0;
assign magma_Bits_2_eq_inst13_out = mode == 2'h0;
assign magma_Bits_2_eq_inst2_out = mode == 2'h1;
assign magma_Bits_2_eq_inst3_out = mode == 2'h0;
assign magma_Bits_2_eq_inst4_out = mode == 2'h0;
assign magma_Bits_2_eq_inst5_out = mode == 2'h0;
assign magma_Bits_2_eq_inst6_out = mode == 2'h1;
assign magma_Bits_2_eq_inst7_out = mode == 2'h1;
assign magma_Bits_2_eq_inst8_out = mode == 2'h1;
assign magma_Bits_2_eq_inst9_out = mode == 2'h1;
endmodule

module RegisterMode (
    input [1:0] mode,
    input [3:0] const_,
    input [3:0] value,
    input clk_en,
    input config_we,
    input [3:0] config_data,
    input CLK,
    output [3:0] O0,
    output [3:0] O1
);
wire [3:0] RegisterMode_comb_inst0_O0;
wire RegisterMode_comb_inst0_O1;
wire [3:0] Register_inst0_O;
RegisterMode_comb RegisterMode_comb_inst0 (
    .mode(mode),
    .const_(const_),
    .value(value),
    .clk_en(clk_en),
    .config_we(config_we),
    .config_data(config_data),
    .self_register_O(Register_inst0_O),
    .O0(RegisterMode_comb_inst0_O0),
    .O1(RegisterMode_comb_inst0_O1),
    .O2(O0),
    .O3(O1)
);
Register Register_inst0 (
    .value(RegisterMode_comb_inst0_O0),
    .en(RegisterMode_comb_inst0_O1),
    .CLK(CLK),
    .O(Register_inst0_O)
);
endmodule

