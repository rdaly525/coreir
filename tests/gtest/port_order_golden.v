module Add8_cin (
    input [7:0] z,
    input [7:0] x,
    output [7:0] a,
    input CIN
);
assign a = 8'((8'(({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,CIN}) + z)) + x);
endmodule

module Sub8 (
    input [7:0] z,
    input [7:0] x,
    output [7:0] a
);
wire [7:0] inst1_z;
wire [7:0] inst1_x;
wire inst1_CIN;
assign inst1_z = z;
assign inst1_x = ~ x;
assign inst1_CIN = 1'b1;
Add8_cin inst1 (
    .z(inst1_z),
    .x(inst1_x),
    .a(a),
    .CIN(inst1_CIN)
);
endmodule

module test_two_ops (
    input [7:0] z,
    input [7:0] x,
    output [7:0] a
);
wire [7:0] inst1_z;
wire [7:0] inst1_x;
assign inst1_z = 8'(z + x);
assign inst1_x = z;
Sub8 inst1 (
    .z(inst1_z),
    .x(inst1_x),
    .a(a)
);
endmodule

