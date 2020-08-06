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
wire [3:0] Mux2xOutBits4_inst0_I0;
wire [3:0] Mux2xOutBits4_inst0_I1;
wire Mux2xOutBits4_inst0_S;
assign Mux2xOutBits4_inst0_I0 = self_value_O;
assign Mux2xOutBits4_inst0_I1 = value;
assign Mux2xOutBits4_inst0_S = en;
Mux2xOutBits4 Mux2xOutBits4_inst0 (
    .I0(Mux2xOutBits4_inst0_I0),
    .I1(Mux2xOutBits4_inst0_I1),
    .S(Mux2xOutBits4_inst0_S),
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
wire [3:0] Register_comb_inst0_value;
wire Register_comb_inst0_en;
wire [3:0] Register_comb_inst0_self_value_O;
wire [3:0] Register_comb_inst0_O0;
wire reg_P_inst0_clk;
wire [3:0] reg_P_inst0_in;
wire [3:0] reg_P_inst0_out;
assign Register_comb_inst0_value = value;
assign Register_comb_inst0_en = en;
assign Register_comb_inst0_self_value_O = reg_P_inst0_out;
Register_comb Register_comb_inst0 (
    .value(Register_comb_inst0_value),
    .en(Register_comb_inst0_en),
    .self_value_O(Register_comb_inst0_self_value_O),
    .O0(Register_comb_inst0_O0),
    .O1(O)
);
assign reg_P_inst0_clk = CLK;
assign reg_P_inst0_in = Register_comb_inst0_O0;
coreir_reg #(
    .clk_posedge(1'b1),
    .init(4'h0),
    .width(4)
) reg_P_inst0 (
    .clk(reg_P_inst0_clk),
    .in(reg_P_inst0_in),
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
wire Mux2xOutBit_inst0_I0;
wire Mux2xOutBit_inst0_I1;
wire Mux2xOutBit_inst0_S;
wire Mux2xOutBit_inst0_O;
wire Mux2xOutBit_inst1_I0;
wire Mux2xOutBit_inst1_I1;
wire Mux2xOutBit_inst1_S;
wire Mux2xOutBit_inst1_O;
wire Mux2xOutBit_inst2_I0;
wire Mux2xOutBit_inst2_I1;
wire Mux2xOutBit_inst2_S;
wire Mux2xOutBit_inst2_O;
wire Mux2xOutBit_inst3_I0;
wire Mux2xOutBit_inst3_I1;
wire Mux2xOutBit_inst3_S;
wire Mux2xOutBit_inst3_O;
wire Mux2xOutBit_inst4_I0;
wire Mux2xOutBit_inst4_I1;
wire Mux2xOutBit_inst4_S;
wire Mux2xOutBit_inst4_O;
wire Mux2xOutBit_inst5_I0;
wire Mux2xOutBit_inst5_I1;
wire Mux2xOutBit_inst5_S;
wire [3:0] Mux2xOutBits4_inst0_I0;
wire [3:0] Mux2xOutBits4_inst0_I1;
wire Mux2xOutBits4_inst0_S;
wire [3:0] Mux2xOutBits4_inst0_O;
wire [3:0] Mux2xOutBits4_inst1_I0;
wire [3:0] Mux2xOutBits4_inst1_I1;
wire Mux2xOutBits4_inst1_S;
wire [3:0] Mux2xOutBits4_inst1_O;
wire [3:0] Mux2xOutBits4_inst10_I0;
wire [3:0] Mux2xOutBits4_inst10_I1;
wire Mux2xOutBits4_inst10_S;
wire [3:0] Mux2xOutBits4_inst10_O;
wire [3:0] Mux2xOutBits4_inst11_I0;
wire [3:0] Mux2xOutBits4_inst11_I1;
wire Mux2xOutBits4_inst11_S;
wire [3:0] Mux2xOutBits4_inst11_O;
wire [3:0] Mux2xOutBits4_inst12_I0;
wire [3:0] Mux2xOutBits4_inst12_I1;
wire Mux2xOutBits4_inst12_S;
wire [3:0] Mux2xOutBits4_inst13_I0;
wire [3:0] Mux2xOutBits4_inst13_I1;
wire Mux2xOutBits4_inst13_S;
wire [3:0] Mux2xOutBits4_inst14_I0;
wire [3:0] Mux2xOutBits4_inst14_I1;
wire Mux2xOutBits4_inst14_S;
wire [3:0] Mux2xOutBits4_inst2_I0;
wire [3:0] Mux2xOutBits4_inst2_I1;
wire Mux2xOutBits4_inst2_S;
wire [3:0] Mux2xOutBits4_inst2_O;
wire [3:0] Mux2xOutBits4_inst3_I0;
wire [3:0] Mux2xOutBits4_inst3_I1;
wire Mux2xOutBits4_inst3_S;
wire [3:0] Mux2xOutBits4_inst3_O;
wire [3:0] Mux2xOutBits4_inst4_I0;
wire [3:0] Mux2xOutBits4_inst4_I1;
wire Mux2xOutBits4_inst4_S;
wire [3:0] Mux2xOutBits4_inst4_O;
wire [3:0] Mux2xOutBits4_inst5_I0;
wire [3:0] Mux2xOutBits4_inst5_I1;
wire Mux2xOutBits4_inst5_S;
wire [3:0] Mux2xOutBits4_inst5_O;
wire [3:0] Mux2xOutBits4_inst6_I0;
wire [3:0] Mux2xOutBits4_inst6_I1;
wire Mux2xOutBits4_inst6_S;
wire [3:0] Mux2xOutBits4_inst6_O;
wire [3:0] Mux2xOutBits4_inst7_I0;
wire [3:0] Mux2xOutBits4_inst7_I1;
wire Mux2xOutBits4_inst7_S;
wire [3:0] Mux2xOutBits4_inst7_O;
wire [3:0] Mux2xOutBits4_inst8_I0;
wire [3:0] Mux2xOutBits4_inst8_I1;
wire Mux2xOutBits4_inst8_S;
wire [3:0] Mux2xOutBits4_inst8_O;
wire [3:0] Mux2xOutBits4_inst9_I0;
wire [3:0] Mux2xOutBits4_inst9_I1;
wire Mux2xOutBits4_inst9_S;
wire [3:0] Mux2xOutBits4_inst9_O;
assign Mux2xOutBit_inst0_I0 = clk_en;
assign Mux2xOutBit_inst0_I1 = 1'b0;
assign Mux2xOutBit_inst0_S = mode == 2'h1;
Mux2xOutBit Mux2xOutBit_inst0 (
    .I0(Mux2xOutBit_inst0_I0),
    .I1(Mux2xOutBit_inst0_I1),
    .S(Mux2xOutBit_inst0_S),
    .O(Mux2xOutBit_inst0_O)
);
assign Mux2xOutBit_inst1_I0 = Mux2xOutBit_inst0_O;
assign Mux2xOutBit_inst1_I1 = 1'b0;
assign Mux2xOutBit_inst1_S = mode == 2'h0;
Mux2xOutBit Mux2xOutBit_inst1 (
    .I0(Mux2xOutBit_inst1_I0),
    .I1(Mux2xOutBit_inst1_I1),
    .S(Mux2xOutBit_inst1_S),
    .O(Mux2xOutBit_inst1_O)
);
assign Mux2xOutBit_inst2_I0 = Mux2xOutBit_inst1_O;
assign Mux2xOutBit_inst2_I1 = 1'b1;
assign Mux2xOutBit_inst2_S = ~ (config_we ^ 1'b1);
Mux2xOutBit Mux2xOutBit_inst2 (
    .I0(Mux2xOutBit_inst2_I0),
    .I1(Mux2xOutBit_inst2_I1),
    .S(Mux2xOutBit_inst2_S),
    .O(Mux2xOutBit_inst2_O)
);
assign Mux2xOutBit_inst3_I0 = clk_en;
assign Mux2xOutBit_inst3_I1 = 1'b0;
assign Mux2xOutBit_inst3_S = mode == 2'h1;
Mux2xOutBit Mux2xOutBit_inst3 (
    .I0(Mux2xOutBit_inst3_I0),
    .I1(Mux2xOutBit_inst3_I1),
    .S(Mux2xOutBit_inst3_S),
    .O(Mux2xOutBit_inst3_O)
);
assign Mux2xOutBit_inst4_I0 = Mux2xOutBit_inst3_O;
assign Mux2xOutBit_inst4_I1 = 1'b0;
assign Mux2xOutBit_inst4_S = mode == 2'h0;
Mux2xOutBit Mux2xOutBit_inst4 (
    .I0(Mux2xOutBit_inst4_I0),
    .I1(Mux2xOutBit_inst4_I1),
    .S(Mux2xOutBit_inst4_S),
    .O(Mux2xOutBit_inst4_O)
);
assign Mux2xOutBit_inst5_I0 = Mux2xOutBit_inst4_O;
assign Mux2xOutBit_inst5_I1 = 1'b1;
assign Mux2xOutBit_inst5_S = ~ (config_we ^ 1'b1);
Mux2xOutBit Mux2xOutBit_inst5 (
    .I0(Mux2xOutBit_inst5_I0),
    .I1(Mux2xOutBit_inst5_I1),
    .S(Mux2xOutBit_inst5_S),
    .O(O1)
);
assign Mux2xOutBits4_inst0_I0 = value;
assign Mux2xOutBits4_inst0_I1 = value;
assign Mux2xOutBits4_inst0_S = mode == 2'h1;
Mux2xOutBits4 Mux2xOutBits4_inst0 (
    .I0(Mux2xOutBits4_inst0_I0),
    .I1(Mux2xOutBits4_inst0_I1),
    .S(Mux2xOutBits4_inst0_S),
    .O(Mux2xOutBits4_inst0_O)
);
assign Mux2xOutBits4_inst1_I0 = self_register_O;
assign Mux2xOutBits4_inst1_I1 = self_register_O;
assign Mux2xOutBits4_inst1_S = mode == 2'h1;
Mux2xOutBits4 Mux2xOutBits4_inst1 (
    .I0(Mux2xOutBits4_inst1_I0),
    .I1(Mux2xOutBits4_inst1_I1),
    .S(Mux2xOutBits4_inst1_S),
    .O(Mux2xOutBits4_inst1_O)
);
assign Mux2xOutBits4_inst10_I0 = Mux2xOutBits4_inst7_O;
assign Mux2xOutBits4_inst10_I1 = const_;
assign Mux2xOutBits4_inst10_S = mode == 2'h0;
Mux2xOutBits4 Mux2xOutBits4_inst10 (
    .I0(Mux2xOutBits4_inst10_I0),
    .I1(Mux2xOutBits4_inst10_I1),
    .S(Mux2xOutBits4_inst10_S),
    .O(Mux2xOutBits4_inst10_O)
);
assign Mux2xOutBits4_inst11_I0 = Mux2xOutBits4_inst8_O;
assign Mux2xOutBits4_inst11_I1 = self_register_O;
assign Mux2xOutBits4_inst11_S = mode == 2'h0;
Mux2xOutBits4 Mux2xOutBits4_inst11 (
    .I0(Mux2xOutBits4_inst11_I0),
    .I1(Mux2xOutBits4_inst11_I1),
    .S(Mux2xOutBits4_inst11_S),
    .O(Mux2xOutBits4_inst11_O)
);
assign Mux2xOutBits4_inst12_I0 = Mux2xOutBits4_inst9_O;
assign Mux2xOutBits4_inst12_I1 = config_data;
assign Mux2xOutBits4_inst12_S = ~ (config_we ^ 1'b1);
Mux2xOutBits4 Mux2xOutBits4_inst12 (
    .I0(Mux2xOutBits4_inst12_I0),
    .I1(Mux2xOutBits4_inst12_I1),
    .S(Mux2xOutBits4_inst12_S),
    .O(O0)
);
assign Mux2xOutBits4_inst13_I0 = Mux2xOutBits4_inst10_O;
assign Mux2xOutBits4_inst13_I1 = self_register_O;
assign Mux2xOutBits4_inst13_S = ~ (config_we ^ 1'b1);
Mux2xOutBits4 Mux2xOutBits4_inst13 (
    .I0(Mux2xOutBits4_inst13_I0),
    .I1(Mux2xOutBits4_inst13_I1),
    .S(Mux2xOutBits4_inst13_S),
    .O(O2)
);
assign Mux2xOutBits4_inst14_I0 = Mux2xOutBits4_inst11_O;
assign Mux2xOutBits4_inst14_I1 = self_register_O;
assign Mux2xOutBits4_inst14_S = ~ (config_we ^ 1'b1);
Mux2xOutBits4 Mux2xOutBits4_inst14 (
    .I0(Mux2xOutBits4_inst14_I0),
    .I1(Mux2xOutBits4_inst14_I1),
    .S(Mux2xOutBits4_inst14_S),
    .O(O3)
);
assign Mux2xOutBits4_inst2_I0 = Mux2xOutBits4_inst0_O;
assign Mux2xOutBits4_inst2_I1 = value;
assign Mux2xOutBits4_inst2_S = mode == 2'h0;
Mux2xOutBits4 Mux2xOutBits4_inst2 (
    .I0(Mux2xOutBits4_inst2_I0),
    .I1(Mux2xOutBits4_inst2_I1),
    .S(Mux2xOutBits4_inst2_S),
    .O(Mux2xOutBits4_inst2_O)
);
assign Mux2xOutBits4_inst3_I0 = Mux2xOutBits4_inst1_O;
assign Mux2xOutBits4_inst3_I1 = self_register_O;
assign Mux2xOutBits4_inst3_S = mode == 2'h0;
Mux2xOutBits4 Mux2xOutBits4_inst3 (
    .I0(Mux2xOutBits4_inst3_I0),
    .I1(Mux2xOutBits4_inst3_I1),
    .S(Mux2xOutBits4_inst3_S),
    .O(Mux2xOutBits4_inst3_O)
);
assign Mux2xOutBits4_inst4_I0 = Mux2xOutBits4_inst2_O;
assign Mux2xOutBits4_inst4_I1 = config_data;
assign Mux2xOutBits4_inst4_S = ~ (config_we ^ 1'b1);
Mux2xOutBits4 Mux2xOutBits4_inst4 (
    .I0(Mux2xOutBits4_inst4_I0),
    .I1(Mux2xOutBits4_inst4_I1),
    .S(Mux2xOutBits4_inst4_S),
    .O(Mux2xOutBits4_inst4_O)
);
assign Mux2xOutBits4_inst5_I0 = Mux2xOutBits4_inst3_O;
assign Mux2xOutBits4_inst5_I1 = self_register_O;
assign Mux2xOutBits4_inst5_S = ~ (config_we ^ 1'b1);
Mux2xOutBits4 Mux2xOutBits4_inst5 (
    .I0(Mux2xOutBits4_inst5_I0),
    .I1(Mux2xOutBits4_inst5_I1),
    .S(Mux2xOutBits4_inst5_S),
    .O(Mux2xOutBits4_inst5_O)
);
assign Mux2xOutBits4_inst6_I0 = value;
assign Mux2xOutBits4_inst6_I1 = value;
assign Mux2xOutBits4_inst6_S = mode == 2'h1;
Mux2xOutBits4 Mux2xOutBits4_inst6 (
    .I0(Mux2xOutBits4_inst6_I0),
    .I1(Mux2xOutBits4_inst6_I1),
    .S(Mux2xOutBits4_inst6_S),
    .O(Mux2xOutBits4_inst6_O)
);
assign Mux2xOutBits4_inst7_I0 = self_register_O;
assign Mux2xOutBits4_inst7_I1 = value;
assign Mux2xOutBits4_inst7_S = mode == 2'h1;
Mux2xOutBits4 Mux2xOutBits4_inst7 (
    .I0(Mux2xOutBits4_inst7_I0),
    .I1(Mux2xOutBits4_inst7_I1),
    .S(Mux2xOutBits4_inst7_S),
    .O(Mux2xOutBits4_inst7_O)
);
assign Mux2xOutBits4_inst8_I0 = self_register_O;
assign Mux2xOutBits4_inst8_I1 = self_register_O;
assign Mux2xOutBits4_inst8_S = mode == 2'h1;
Mux2xOutBits4 Mux2xOutBits4_inst8 (
    .I0(Mux2xOutBits4_inst8_I0),
    .I1(Mux2xOutBits4_inst8_I1),
    .S(Mux2xOutBits4_inst8_S),
    .O(Mux2xOutBits4_inst8_O)
);
assign Mux2xOutBits4_inst9_I0 = Mux2xOutBits4_inst6_O;
assign Mux2xOutBits4_inst9_I1 = value;
assign Mux2xOutBits4_inst9_S = mode == 2'h0;
Mux2xOutBits4 Mux2xOutBits4_inst9 (
    .I0(Mux2xOutBits4_inst9_I0),
    .I1(Mux2xOutBits4_inst9_I1),
    .S(Mux2xOutBits4_inst9_S),
    .O(Mux2xOutBits4_inst9_O)
);
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
wire [1:0] RegisterMode_comb_inst0_mode;
wire [3:0] RegisterMode_comb_inst0_const_;
wire [3:0] RegisterMode_comb_inst0_value;
wire RegisterMode_comb_inst0_clk_en;
wire RegisterMode_comb_inst0_config_we;
wire [3:0] RegisterMode_comb_inst0_config_data;
wire [3:0] RegisterMode_comb_inst0_self_register_O;
wire [3:0] RegisterMode_comb_inst0_O0;
wire RegisterMode_comb_inst0_O1;
wire [3:0] Register_inst0_value;
wire Register_inst0_en;
wire Register_inst0_CLK;
wire [3:0] Register_inst0_O;
assign RegisterMode_comb_inst0_mode = mode;
assign RegisterMode_comb_inst0_const_ = const_;
assign RegisterMode_comb_inst0_value = value;
assign RegisterMode_comb_inst0_clk_en = clk_en;
assign RegisterMode_comb_inst0_config_we = config_we;
assign RegisterMode_comb_inst0_config_data = config_data;
assign RegisterMode_comb_inst0_self_register_O = Register_inst0_O;
RegisterMode_comb RegisterMode_comb_inst0 (
    .mode(RegisterMode_comb_inst0_mode),
    .const_(RegisterMode_comb_inst0_const_),
    .value(RegisterMode_comb_inst0_value),
    .clk_en(RegisterMode_comb_inst0_clk_en),
    .config_we(RegisterMode_comb_inst0_config_we),
    .config_data(RegisterMode_comb_inst0_config_data),
    .self_register_O(RegisterMode_comb_inst0_self_register_O),
    .O0(RegisterMode_comb_inst0_O0),
    .O1(RegisterMode_comb_inst0_O1),
    .O2(O0),
    .O3(O1)
);
assign Register_inst0_value = RegisterMode_comb_inst0_O0;
assign Register_inst0_en = RegisterMode_comb_inst0_O1;
assign Register_inst0_CLK = CLK;
Register Register_inst0 (
    .value(Register_inst0_value),
    .en(Register_inst0_en),
    .CLK(Register_inst0_CLK),
    .O(Register_inst0_O)
);
endmodule

