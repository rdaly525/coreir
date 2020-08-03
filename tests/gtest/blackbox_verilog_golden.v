// This is an important comment for foo!!
module foo (input I, output O);
    assign O = I;
endmodule
module top (
    input I,
    output O
);
wire inst0_I;
assign inst0_I = I;
foo inst0 (
    .I(inst0_I),
    .O(O)
);
endmodule

