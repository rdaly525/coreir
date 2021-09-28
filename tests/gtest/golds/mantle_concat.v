module mantle_concatArrT__t1BitIn329__t2BitIn326 (
    input [31:0] in1 [8:0],
    input [31:0] in2 [5:0],
    output [31:0] out [14:0]
);
assign out[14] = in2[5];
assign out[13] = in2[4];
assign out[12] = in2[3];
assign out[11] = in2[2];
assign out[10] = in2[1];
assign out[9] = in2[0];
assign out[8] = in1[8];
assign out[7] = in1[7];
assign out[6] = in1[6];
assign out[5] = in1[5];
assign out[4] = in1[4];
assign out[3] = in1[3];
assign out[2] = in1[2];
assign out[1] = in1[1];
assign out[0] = in1[0];
endmodule

module Foo (
    input [31:0] I0 [8:0],
    input [31:0] I1 [5:0],
    output [31:0] O [14:0]
);
mantle_concatArrT__t1BitIn329__t2BitIn326 concat (
    .in1(I0),
    .in2(I1),
    .out(O)
);
endmodule

