// This is an important comment for foo!!
module foo (input I, output O);
    assign O = I;
endmodule
module top (input I, output O);
wire inst0_O__inst1_I;
foo inst0(.I(I), .O(inst0_O__inst1_I));
foo inst1(.I(inst0_O__inst1_I), .O(O));
endmodule

