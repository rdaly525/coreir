// Module `coreir_reg__width16_src` defined externally
// Module `coreir_reg__width16_snk` defined externally
module mantle_wire__typeBitIn16 (
    output [15:0] in,
    input [15:0] out
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
    output [15:0] out,
    input CLK
);
wire [15:0] _$0_in;
wire [15:0] _$1_out;
wire [15:0] value_src_out;
mantle_wire__typeBitIn16 _$0 (
    .in(_$0_in),
    .out({in[7:0],in[15:8]})
);
mantle_wire__typeBit16 _$1 (
    .in(value_src_out),
    .out(_$1_out)
);
coreir_reg__width16_snk value_snk (
    .clk(CLK),
    .in(_$0_in)
);
coreir_reg__width16_src value_src (
    .out(value_src_out)
);
assign out = {_$1_out[7:0],_$1_out[15:8]};
endmodule

