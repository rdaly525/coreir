// This is an important comment for foo!!
module foo (input [3:0] I, output [3:0] O);
    assign O = I;
endmodule
module top (
    input [3:0] self_I,
    output [3:0] O
);
wire [3:0] inst0_O;
wire [3:0] inst1_O;
wire [3:0] inst0_I;
assign inst0_I = {self_I[2],self_I[1],self_I[0],self_I[0]};
foo inst0 (
    .I(inst0_I),
    .O(inst0_O)
);
wire [3:0] inst1_I;
assign inst1_I = {self_I[1],inst0_O[1],inst0_O[1],inst0_O[0]};
foo inst1 (
    .I(inst1_I),
    .O(inst1_O)
);
assign O = {self_I[1],self_I[0],inst1_O[0],inst1_O[0]};
endmodule

