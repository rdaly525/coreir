module coreir_slice #(parameter hi = 32'd1, parameter lo = 32'd0, parameter width = 32'd1) (input [width-1:0] in, output [hi-lo-1:0] out);
  assign out = in[hi-1:lo];
endmodule

module coreir_concat #(parameter width0 = 32'd1, parameter width1 = 32'd1) (input [width0-1:0] in0, input [width1-1:0] in1, output [width0+width1-1:0] out);
  assign out = {in1,in0};
endmodule

module concats (input in, output out);
wire s0_out__cc0_in0;
wire s1_out__cc0_in1;
coreir_concat #(.width0(32'd4), .width1(32'd12)) cc0(.in0(s0_out__cc0_in0), .in1(s1_out__cc0_in1), .out(out));
coreir_slice #(.hi(32'd16), .lo(32'd12), .width(32'd16)) s0(.in(in), .out(s0_out__cc0_in0));
coreir_slice #(.hi(32'd15), .lo(32'd3), .width(32'd16)) s1(.in(in), .out(s1_out__cc0_in1));
endmodule

