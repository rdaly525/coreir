module Add8_cin (
    input [7:0] I0,
    input [7:0] I1,
    output [7:0] O,
    input CIN
);
assign O = (({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,CIN}) + I0) + I1;
endmodule

module Sub8 (
    input [7:0] I0,
    input [7:0] I1,
    output [7:0] O
);
Add8_cin inst1 (
    .I0(I0),
    .I1(~ I1),
    .O(O),
    .CIN(1'b1)
);
endmodule

module test_two_ops (
    input [7:0] I0,
    input [7:0] I1,
    output [7:0] O
);
Sub8 inst1 (
    .I0(I0 + I1),
    .I1(I0),
    .O(O)
);
endmodule

