// This is an important comment for foo!!
module foo (input [3:0] I, output [3:0] O);
    assign O = I;
endmodule
module top (output [3:0] O, input [3:0] self_I);
wire [3:0] inst0_O;
wire [3:0] inst1_O;
foo inst0(.I({self_I[0],self_I[0],self_I[1],self_I[2]}), .O(inst0_O));
foo inst1(.I({inst0_O[0],inst0_O[1],inst0_O[1],self_I[1]}), .O(inst1_O));
assign O = {inst1_O[0],inst1_O[0],self_I[0],self_I[1]};
endmodule

