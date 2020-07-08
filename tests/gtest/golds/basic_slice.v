module mantle_wire__typeBitIn8 (
    output [7:0] in,
    input [7:0] out
);
assign in = out;
endmodule

module mantle_wire__typeBitIn4 (
    output [3:0] in,
    input [3:0] out
);
assign in = out;
endmodule

module mantle_wire__typeBit16 (
    input [15:0] in,
    output [15:0] out
);
assign out = in;
endmodule

module top (
    input [15:0] in,
    output [3:0] out0_0,
    output [3:0] out0_1,
    output [7:0] out1
);
wire [15:0] _$_U1_out;
mantle_wire__typeBit16 _$_U1 (
    .in(in),
    .out(_$_U1_out)
);
mantle_wire__typeBitIn4 _$_U2 (
    .in(out0_0),
    .out({_$_U1_out[1:0],_$_U1_out[3:2]})
);
mantle_wire__typeBitIn8 _$_U3 (
    .in(out1),
    .out({_$_U1_out[15:12],_$_U1_out[11:8]})
);
assign out0_1 = _$_U1_out[7:4];
endmodule

