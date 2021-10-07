module mantle_liftArrT__tBit1 (
    input in,
    output [0:0] out
);
assign out = in;
endmodule

module Foo (
    input I,
    output [0:0] O
);
mantle_liftArrT__tBit1 lift (
    .in(I),
    .out(O)
);
endmodule

