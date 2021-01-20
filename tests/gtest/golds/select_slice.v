module top (
    input [15:0] in,
    output [1:0] out
);
assign out = {in[15:9][5],in[7:0][3]};
endmodule

