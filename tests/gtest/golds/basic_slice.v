module top (
    input [15:0] in,
    output [3:0] out0_0,
    output [3:0] out0_1,
    output [7:0] out1
);
assign out0_0 = {in[1:0],in[3:2]};
assign out0_1 = in[7:4];
assign out1 = {in[15:12],in[11:8]};
endmodule

