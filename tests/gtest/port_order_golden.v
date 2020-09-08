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
wire [7:0] inst0_out;
assign inst0_out = ~ x;
Add8_cin inst1 (
    .z(z),
    .x(inst0_out),
    .a(a),
    .CIN(1'b1)
);
endmodule

module test_two_ops (
    input [7:0] z,
    input [7:0] x,
    output [7:0] a
);
wire [7:0] inst0_out;
assign inst0_out = 8'(z + x);
Sub8 inst1 (
    .z(inst0_out),
    .x(z),
    .a(a)
);
endmodule

