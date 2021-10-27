module mantle_slicesArrT__slices7386__tBitIn329 (
    input [31:0] in [8:0],
    output [31:0] out0 [3:0],
    output [31:0] out1 [1:0]
);
assign out0[3] = in[6];
assign out0[2] = in[5];
assign out0[1] = in[4];
assign out0[0] = in[3];
assign out1[1] = in[7];
assign out1[0] = in[6];
endmodule

module Foo (
    input [31:0] I [8:0],
    output [31:0] O0 [3:0],
    output [31:0] O1 [1:0]
);
mantle_slicesArrT__slices7386__tBitIn329 slices (
    .in(I),
    .out0(O0),
    .out1(O1)
);
endmodule

