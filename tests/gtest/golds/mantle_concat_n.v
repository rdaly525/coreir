module mantle_concatNArrT__Ns967__t_childBitIn32 (
    input [31:0] in0 [8:0],
    input [31:0] in1 [5:0],
    input [31:0] in2 [6:0],
    output [31:0] out [21:0]
);
assign out[21] = in2[6];
assign out[20] = in2[5];
assign out[19] = in2[4];
assign out[18] = in2[3];
assign out[17] = in2[2];
assign out[16] = in2[1];
assign out[15] = in2[0];
assign out[14] = in1[5];
assign out[13] = in1[4];
assign out[12] = in1[3];
assign out[11] = in1[2];
assign out[10] = in1[1];
assign out[9] = in1[0];
assign out[8] = in0[8];
assign out[7] = in0[7];
assign out[6] = in0[6];
assign out[5] = in0[5];
assign out[4] = in0[4];
assign out[3] = in0[3];
assign out[2] = in0[2];
assign out[1] = in0[1];
assign out[0] = in0[0];
endmodule

module Foo (
    input [31:0] I0 [8:0],
    input [31:0] I1 [5:0],
    input [31:0] I2 [6:0],
    output [31:0] O [21:0]
);
mantle_concatNArrT__Ns967__t_childBitIn32 concat (
    .in0(I0),
    .in1(I1),
    .in2(I2),
    .out(O)
);
endmodule

