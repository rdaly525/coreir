module Add8_cin (input CIN, input [7:0] I0, input [7:0] I1, output [7:0] O);
wire bit_const_0_None_out;
wire [7:0] inst0_out;
wire [7:0] inst1_out;
assign bit_const_0_None_out = 0;
assign inst0_out = inst1_out + I1;
assign inst1_out = ({bit_const_0_None_out,bit_const_0_None_out,bit_const_0_None_out,bit_const_0_None_out,bit_const_0_None_out,bit_const_0_None_out,bit_const_0_None_out,CIN}) + I0;
assign O = inst0_out;
endmodule

module Sub8 (input [7:0] I0, input [7:0] I1, output [7:0] O);
wire bit_const_1_None_out;
wire [7:0] inst0_out;
wire [7:0] inst1_O;
assign bit_const_1_None_out = 1;
assign inst0_out = ~ I1;
Add8_cin inst1(.CIN(bit_const_1_None_out), .I0(I0), .I1(inst0_out), .O(inst1_O));
assign O = inst1_O;
endmodule

module test_two_ops (input [7:0] I0, input [7:0] I1, output [7:0] O);
wire [7:0] inst0_out;
wire [7:0] inst1_O;
assign inst0_out = I0 + I1;
Sub8 inst1(.I0(inst0_out), .I1(I0), .O(inst1_O));
assign O = inst1_O;
endmodule

