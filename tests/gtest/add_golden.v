module Top (input [7:0] I0, input [7:0] I1, output [7:0] O);
wire [7:0] inst0_out;
assign inst0_out = I0 + I1;
assign O = inst0_out;
endmodule

