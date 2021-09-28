module mantle_getT__i7__tBitIn329 (
    input [31:0] in [8:0],
    output [31:0] out
);
assign out = in[7];
endmodule

module Foo (
    input [31:0] I [8:0],
    output [31:0] O
);
mantle_getT__i7__tBitIn329 get (
    .in(I),
    .out(O)
);
endmodule

