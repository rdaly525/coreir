// This is an important comment for foo!!
module foo (input [3:0] I, output [3:0] O);
    assign O = I;
endmodule
module top (input [3:0] I, output [3:0] O);
wire [3:0] inst0_O;
wire [3:0] inst1_O;
foo inst0(.I({I[0],I[0],I[1],I[2]}), .O(inst0_O));
foo inst1(.I({inst0_O[0],inst0_O[1],inst0_O[1],I[1]}), .O(inst1_O));
assign O = {inst1_O[0],inst1_O[0],I[0],I[1]};
endmodule

