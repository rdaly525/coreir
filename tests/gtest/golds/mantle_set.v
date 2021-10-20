module mantle_setIdxArrT__i7__tBitIn329 (
    input [31:0] in [8:0],
    input [31:0] val,
    output [31:0] out [8:0]
);
assign out[8] = in[8];
assign out[7] = val;
assign out[6] = in[6];
assign out[5] = in[5];
assign out[4] = in[4];
assign out[3] = in[3];
assign out[2] = in[2];
assign out[1] = in[1];
assign out[0] = in[0];
endmodule

module Foo (
    input [31:0] I [8:0],
    output [31:0] O [8:0]
);
mantle_setIdxArrT__i7__tBitIn329 set (
    .in(I),
    .val(I[3]),
    .out(O)
);
endmodule

