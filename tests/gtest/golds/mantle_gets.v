module mantle_getsArrT__gets78__tBitIn329 (
    input [31:0] in [8:0],
    output [31:0] out0,
    output [31:0] out1
);
assign out0 = in[7];
assign out1 = in[8];
endmodule

module Foo (
    input [31:0] I [8:0],
    output [31:0] O0,
    output [31:0] O1
);
mantle_getsArrT__gets78__tBitIn329 gets (
    .in(I),
    .out0(O0),
    .out1(O1)
);
endmodule

