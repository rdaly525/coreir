module Add8_cin (input [7:0] z, input [7:0] x, output [7:0] a, input CIN);
assign a = (({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,CIN}) + z) + x;
endmodule

module Sub8 (input [7:0] z, input [7:0] x, output [7:0] a);
Add8_cin inst1(.z(z), .x(~ x), .a(a), .CIN(1'b1));
endmodule

module test_two_ops (input [7:0] z, input [7:0] x, output [7:0] a);
Sub8 inst1(.z(z + x), .x(z), .a(a));
endmodule

