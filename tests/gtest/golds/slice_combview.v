// Module `coreir_coreir_reg__width16_src` defined externally
// Module `coreir_coreir_reg__width16_snk` defined externally
module top (
    input [15:0] in,
    output [15:0] out,
    input CLK
);
wire [15:0] value_in;
wire [15:0] value_src_out;
assign value_in = {in[7:0],in[15:8]};
coreir_coreir_reg__width16_snk value_snk (
    .clk(CLK),
    .in(value_in)
);
coreir_coreir_reg__width16_src value_src (
    .out(value_src_out)
);
assign out = {value_src_out[7:0],value_src_out[15:8]};
endmodule

