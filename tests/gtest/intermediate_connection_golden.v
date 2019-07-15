// This is an important comment for foo!!
module foo (input I, output O);
    assign O = I;
endmodule
module top (input I, output O);
wire inst0_O;
wire inst1_O;
foo inst0(.I(I), .O(inst0_O));
foo inst1(.I(inst0_O), .O(inst1_O));
assign O = inst1_O;
endmodule

