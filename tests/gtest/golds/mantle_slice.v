module mantle_sliceT__hi7__lo3__tBitIn329 (
    input [31:0] in [8:0],
    output [31:0] out [3:0]
);
assign out[3] = in[6];
assign out[2] = in[5];
assign out[1] = in[4];
assign out[0] = in[3];
endmodule

module Foo (
    input [31:0] I [8:0],
    output [31:0] O [3:0]
);
mantle_sliceT__hi7__lo3__tBitIn329 slice (
    .in(I),
    .out(O)
);
endmodule

