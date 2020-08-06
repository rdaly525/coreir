// This is an important comment for foo!!
module foo (input I, inout IO, output O);
    assign O = I;
    assign IO = I;
endmodule
module top (
    input I,
    inout IO0,
    inout IO1,
    output O
);
wire inst0_I;
wire inst0_IO;
wire inst0_O;
wire inst1_I;
wire inst1_IO;
assign inst0_I = I;
foo inst0 (
    .I(inst0_I),
    .IO(inst0_IO),
    .O(inst0_O)
);
assign inst1_I = inst0_O;
foo inst1 (
    .I(inst1_I),
    .IO(inst1_IO),
    .O(O)
);
assign inst0_IO = inst1_IO;
assign inst0_IO = IO0;
assign inst0_IO = IO1;
endmodule

