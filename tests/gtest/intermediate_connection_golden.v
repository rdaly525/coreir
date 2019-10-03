// This is an important comment for foo!!
module foo (input I, inout IO, output O);
    assign O = I;
    assign IO = I;
endmodule
module top (input I, inout IO0, inout IO1, output O);
wire inst0_IO;
wire inst0_O;
wire inst1_IO;
wire inst1_O;
foo inst0(.I(I), .IO(inst0_IO), .O(inst0_O));
foo inst1(.I(inst0_O), .IO(inst1_IO), .O(inst1_O));
assign O = inst1_O;
assign inst0_IO = inst1_IO;
assign IO0 = inst0_IO;
assign inst0_IO = IO1;
endmodule

