// Module `coreir_reg__width16_src` defined externally
// Module `coreir_reg__width16_snk` defined externally
module top (
    input [15:0] in,
    output [15:0] out,
    input CLK
);
wire [15:0] _$_U1;
wire [15:0] value_src_out;
assign _$_U1 = {in[7:0],in[15:8]};
coreir_coreir_reg__width16_snk value_snk (
    .clk(CLK),
    .in(_$_U1)
);
coreir_coreir_reg__width16_src value_src (
    .out(value_src_out)
);
assign out = {value_src_out[7:0],value_src_out[15:8]};
endmodule

