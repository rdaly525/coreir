module coreir_reg #(parameter width = 1, parameter clk_posedge = 1, parameter init = 1) (input clk, input [width-1:0] in, output [width-1:0] out);
  reg [width-1:0] outReg=init;
  wire real_clk;
  assign real_clk = clk_posedge ? clk : ~clk;
  always @(posedge real_clk) begin
    outReg <= in;
  end
  assign out = outReg;
endmodule

module commonlib_muxn__N2__width4 (input [3:0] in_data_0, input [3:0] in_data_1, input [0:0] in_sel, output [3:0] out);
assign out = in_sel[0] ? in_data_1 : in_data_0;
endmodule

module commonlib_muxn__N2__width1 (input [0:0] in_data_0, input [0:0] in_data_1, input [0:0] in_sel, output [0:0] out);
assign out = in_sel[0] ? in_data_1 : in_data_0;
endmodule

module Mux2xOutBits4 (input [3:0] I0, input [3:0] I1, output [3:0] O, input S);
commonlib_muxn__N2__width4 coreir_commonlib_mux2x4_inst0(.in_data_0(I0), .in_data_1(I1), .in_sel(S), .out(O));
endmodule

module Register_comb (output [3:0] O0, output [3:0] O1, input en, input [3:0] self_value_O, input [3:0] value);
Mux2xOutBits4 Mux2xOutBits4_inst0(.I0(self_value_O), .I1(value), .O(O0), .S(en));
assign O1 = self_value_O;
endmodule

module Register (input CLK, output [3:0] O, input en, input [3:0] value);
wire [3:0] Register_comb_inst0_O0;
wire [3:0] reg_P_inst0_out;
Register_comb Register_comb_inst0(.O0(Register_comb_inst0_O0), .O1(O), .en(en), .self_value_O(reg_P_inst0_out), .value(value));
coreir_reg #(.clk_posedge(1'b1), .init(4'h0), .width(4)) reg_P_inst0(.clk(CLK), .in(Register_comb_inst0_O0), .out(reg_P_inst0_out));
endmodule

module Mux2xOutBit (input I0, input I1, output O, input S);
wire [0:0] coreir_commonlib_mux2x1_inst0_out;
commonlib_muxn__N2__width1 coreir_commonlib_mux2x1_inst0(.in_data_0(I0), .in_data_1(I1), .in_sel(S), .out(coreir_commonlib_mux2x1_inst0_out));
assign O = coreir_commonlib_mux2x1_inst0_out[0];
endmodule

module RegisterMode_comb (output [3:0] O0, output O1, output [3:0] O2, output [3:0] O3, input clk_en, input [3:0] config_data, input config_we, input [3:0] const_, input [1:0] mode, input [3:0] self_register_O, input [3:0] value);
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
Mux2xOutBit Mux2xOutBit_inst0(.I0(clk_en), .I1(1'b0), .O(Mux2xOutBit_inst0_O), .S(mode == 2'h1));
Mux2xOutBit Mux2xOutBit_inst1(.I0(Mux2xOutBit_inst0_O), .I1(1'b0), .O(Mux2xOutBit_inst1_O), .S(mode == 2'h0));
Mux2xOutBit Mux2xOutBit_inst2(.I0(Mux2xOutBit_inst1_O), .I1(1'b1), .O(Mux2xOutBit_inst2_O), .S(~ (config_we ^ 1'b1)));
Mux2xOutBit Mux2xOutBit_inst3(.I0(clk_en), .I1(1'b0), .O(Mux2xOutBit_inst3_O), .S(mode == 2'h1));
Mux2xOutBit Mux2xOutBit_inst4(.I0(Mux2xOutBit_inst3_O), .I1(1'b0), .O(Mux2xOutBit_inst4_O), .S(mode == 2'h0));
Mux2xOutBit Mux2xOutBit_inst5(.I0(Mux2xOutBit_inst4_O), .I1(1'b1), .O(O1), .S(~ (config_we ^ 1'b1)));
Mux2xOutBits4 Mux2xOutBits4_inst0(.I0(value), .I1(value), .O(Mux2xOutBits4_inst0_O), .S(mode == 2'h1));
Mux2xOutBits4 Mux2xOutBits4_inst1(.I0(self_register_O), .I1(self_register_O), .O(Mux2xOutBits4_inst1_O), .S(mode == 2'h1));
Mux2xOutBits4 Mux2xOutBits4_inst10(.I0(Mux2xOutBits4_inst7_O), .I1(const_), .O(Mux2xOutBits4_inst10_O), .S(mode == 2'h0));
Mux2xOutBits4 Mux2xOutBits4_inst11(.I0(Mux2xOutBits4_inst8_O), .I1(self_register_O), .O(Mux2xOutBits4_inst11_O), .S(mode == 2'h0));
Mux2xOutBits4 Mux2xOutBits4_inst12(.I0(Mux2xOutBits4_inst9_O), .I1(config_data), .O(O0), .S(~ (config_we ^ 1'b1)));
Mux2xOutBits4 Mux2xOutBits4_inst13(.I0(Mux2xOutBits4_inst10_O), .I1(self_register_O), .O(O2), .S(~ (config_we ^ 1'b1)));
Mux2xOutBits4 Mux2xOutBits4_inst14(.I0(Mux2xOutBits4_inst11_O), .I1(self_register_O), .O(O3), .S(~ (config_we ^ 1'b1)));
Mux2xOutBits4 Mux2xOutBits4_inst2(.I0(Mux2xOutBits4_inst0_O), .I1(value), .O(Mux2xOutBits4_inst2_O), .S(mode == 2'h0));
Mux2xOutBits4 Mux2xOutBits4_inst3(.I0(Mux2xOutBits4_inst1_O), .I1(self_register_O), .O(Mux2xOutBits4_inst3_O), .S(mode == 2'h0));
Mux2xOutBits4 Mux2xOutBits4_inst4(.I0(Mux2xOutBits4_inst2_O), .I1(config_data), .O(Mux2xOutBits4_inst4_O), .S(~ (config_we ^ 1'b1)));
Mux2xOutBits4 Mux2xOutBits4_inst5(.I0(Mux2xOutBits4_inst3_O), .I1(self_register_O), .O(Mux2xOutBits4_inst5_O), .S(~ (config_we ^ 1'b1)));
Mux2xOutBits4 Mux2xOutBits4_inst6(.I0(value), .I1(value), .O(Mux2xOutBits4_inst6_O), .S(mode == 2'h1));
Mux2xOutBits4 Mux2xOutBits4_inst7(.I0(self_register_O), .I1(value), .O(Mux2xOutBits4_inst7_O), .S(mode == 2'h1));
Mux2xOutBits4 Mux2xOutBits4_inst8(.I0(self_register_O), .I1(self_register_O), .O(Mux2xOutBits4_inst8_O), .S(mode == 2'h1));
Mux2xOutBits4 Mux2xOutBits4_inst9(.I0(Mux2xOutBits4_inst6_O), .I1(value), .O(Mux2xOutBits4_inst9_O), .S(mode == 2'h0));
endmodule

module RegisterMode (input CLK, output [3:0] O0, output [3:0] O1, input clk_en, input [3:0] config_data, input config_we, input [3:0] const_, input [1:0] mode, input [3:0] value);
wire [3:0] RegisterMode_comb_inst0_O0;
wire RegisterMode_comb_inst0_O1;
wire [3:0] Register_inst0_O;
RegisterMode_comb RegisterMode_comb_inst0(.O0(RegisterMode_comb_inst0_O0), .O1(RegisterMode_comb_inst0_O1), .O2(O0), .O3(O1), .clk_en(clk_en), .config_data(config_data), .config_we(config_we), .const_(const_), .mode(mode), .self_register_O(Register_inst0_O), .value(value));
Register Register_inst0(.CLK(CLK), .O(Register_inst0_O), .en(RegisterMode_comb_inst0_O1), .value(RegisterMode_comb_inst0_O0));
endmodule

