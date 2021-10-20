module mantle_setSliceArrT__hi7__lo3__tBitIn329 (
    input [31:0] in [8:0],
    input [31:0] val [3:0],
    output [31:0] out [8:0]
);
assign out[8] = in[8];
assign out[7] = in[7];
assign out[6] = val[3];
assign out[5] = val[2];
assign out[4] = val[1];
assign out[3] = val[0];
assign out[2] = in[2];
assign out[1] = in[1];
assign out[0] = in[0];
endmodule

module Foo (
    input [31:0] I [8:0],
    output [31:0] O [8:0]
);
wire [31:0] set_val [3:0];
assign set_val[3] = I[3];
assign set_val[2] = I[2];
assign set_val[1] = I[1];
assign set_val[0] = I[0];
mantle_setSliceArrT__hi7__lo3__tBitIn329 set (
    .in(I),
    .val(set_val),
    .out(O)
);
endmodule

