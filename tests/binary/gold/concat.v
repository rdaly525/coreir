module coreir_slice #(parameter hi=1, parameter lo=0, parameter width=1) (
  input [width-1:0] in,
  output [hi-lo-1:0] out
);
  assign out = in[hi-1:lo];

endmodule  // coreir_slice

module coreir_concat #(parameter width0=1, parameter width1=1) (
  input [width0-1:0] in0,
  input [width1-1:0] in1,
  output [width0+width1-1:0] out
);
  assign out = {in1,in0};

endmodule  // coreir_concat

module concats (
  input [15:0] in,
  output [15:0] out
);


  // Instancing generated Module: coreir.concat(width0:4, width1:12)
  wire [3:0] cc0__in0;
  wire [11:0] cc0__in1;
  wire [15:0] cc0__out;
  coreir_concat #(.width0(4),.width1(12)) cc0(
    .in0(cc0__in0),
    .in1(cc0__in1),
    .out(cc0__out)
  );

  // Instancing generated Module: coreir.slice(hi:16, lo:12, width:16)
  wire [15:0] s0__in;
  wire [3:0] s0__out;
  coreir_slice #(.hi(16),.lo(12),.width(16)) s0(
    .in(s0__in),
    .out(s0__out)
  );

  // Instancing generated Module: coreir.slice(hi:15, lo:3, width:16)
  wire [15:0] s1__in;
  wire [11:0] s1__out;
  coreir_slice #(.hi(15),.lo(3),.width(16)) s1(
    .in(s1__in),
    .out(s1__out)
  );

  assign out[15:0] = cc0__out[15:0];


endmodule  // concats

