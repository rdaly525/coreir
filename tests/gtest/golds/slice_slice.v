module top (
    input [15:0] in,
    output [3:0] out
);
assign out = in[7:0][5:2];
endmodule

