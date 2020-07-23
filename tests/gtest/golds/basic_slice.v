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
assign out0_0 = {in[1:0],in[3:2]};
assign out0_1 = in[7:4];
assign out1 = {in[15:12],in[11:8]};
endmodule

