// This is an important comment for foo!!
module foo (input I, output O);
    assign O = I;
endmodule
module top (
    input I,
    output O
);
foo inst0 (
    .I(I),
    .O(O)
);
endmodule

