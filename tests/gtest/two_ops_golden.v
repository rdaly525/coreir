module Add8_cin (input CIN, input [7:0] I0, input [7:0] I1, output [7:0] O);
assign O = (({0,0,0,0,0,0,0,CIN}) + I0) + I1;
endmodule

module Sub8 (input [7:0] I0, input [7:0] I1, output [7:0] O);
wire [7:0] inst1_O;
Add8_cin inst1(.CIN(1), .I0(I0), .I1(~ I1), .O(inst1_O));
assign O = inst1_O;
endmodule

module test_two_ops (input [7:0] I0, input [7:0] I1, output [7:0] O);
wire [7:0] inst1_O;
Sub8 inst1(.I0(I0 + I1), .I1(I0), .O(inst1_O));
assign O = inst1_O;
endmodule

