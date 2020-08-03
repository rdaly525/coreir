module coreir_slice #(
    parameter hi = 1,
    parameter lo = 0,
    parameter width = 1
) (
    input [width-1:0] in,
    output [hi-lo-1:0] out
);
  assign out = in[hi-1:lo];
endmodule

module coreir_concat #(
    parameter width0 = 1,
    parameter width1 = 1
) (
    input [width0-1:0] in0,
    input [width1-1:0] in1,
    output [width0+width1-1:0] out
);
  assign out = {in1,in0};
endmodule

module concats (
    input [15:0] in,
    output [15:0] out
);
wire [3:0] cc0_in0;
wire [11:0] cc0_in1;
wire [15:0] cc0_out;
wire [15:0] s0_in;
wire [3:0] s0_out;
wire [15:0] s1_in;
wire [11:0] s1_out;
assign cc0_in0 = s0_out;
assign cc0_in1 = s1_out;
coreir_concat #(
    .width0(4),
    .width1(12)
) cc0 (
    .in0(cc0_in0),
    .in1(cc0_in1),
    .out(cc0_out)
);
assign s0_in = in;
coreir_slice #(
    .hi(16),
    .lo(12),
    .width(16)
) s0 (
    .in(s0_in),
    .out(s0_out)
);
assign s1_in = in;
coreir_slice #(
    .hi(15),
    .lo(3),
    .width(16)
) s1 (
    .in(s1_in),
    .out(s1_out)
);
assign out = cc0_out;
endmodule

