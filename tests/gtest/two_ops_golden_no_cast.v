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
wire [7:0] inst1_I0;
wire [7:0] inst1_I1;
wire inst1_CIN;
assign inst1_I0 = I0;
assign inst1_I1 = ~ I1;
assign inst1_CIN = 1'b1;
Add8_cin inst1 (
    .I0(inst1_I0),
    .I1(inst1_I1),
    .O(O),
    .CIN(inst1_CIN)
);
endmodule

module test_two_ops (
    input [7:0] I0,
    input [7:0] I1,
    output [7:0] O
);
wire [7:0] inst1_I0;
wire [7:0] inst1_I1;
assign inst1_I0 = I0 + I1;
assign inst1_I1 = I0;
Sub8 inst1 (
    .I0(inst1_I0),
    .I1(inst1_I1),
    .O(O)
);
endmodule

