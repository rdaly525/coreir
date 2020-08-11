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

module coreir_mux #(
    parameter width = 1
) (
    input [width-1:0] in0,
    input [width-1:0] in1,
    input sel,
    output [width-1:0] out
);
  assign out = sel ? in1 : in0;
endmodule

module corebit_term (
    input in
);

endmodule

module commonlib_muxn__N2__width32 (
    input [31:0] in_data [1:0],
    input [0:0] in_sel,
    output [31:0] out
);
wire [31:0] _join_out;
coreir_mux #(
    .width(32)
) _join (
    .in0(in_data[0]),
    .in1(in_data[1]),
    .sel(in_sel[0]),
    .out(_join_out)
);
assign out = _join_out;
endmodule

module commonlib_muxn__N4__width32 (
    input [31:0] in_data [3:0],
    input [1:0] in_sel,
    output [31:0] out
);
wire [31:0] _join_out;
wire [31:0] muxN_0_out;
wire [31:0] muxN_1_out;
wire [0:0] sel_slice0_out;
wire [0:0] sel_slice1_out;
coreir_mux #(
    .width(32)
) _join (
    .in0(muxN_0_out),
    .in1(muxN_1_out),
    .sel(in_sel[1]),
    .out(_join_out)
);
wire [31:0] muxN_0_in_data [1:0];
assign muxN_0_in_data[1] = in_data[1];
assign muxN_0_in_data[0] = in_data[0];
commonlib_muxn__N2__width32 muxN_0 (
    .in_data(muxN_0_in_data),
    .in_sel(sel_slice0_out),
    .out(muxN_0_out)
);
wire [31:0] muxN_1_in_data [1:0];
assign muxN_1_in_data[1] = in_data[3];
assign muxN_1_in_data[0] = in_data[2];
commonlib_muxn__N2__width32 muxN_1 (
    .in_data(muxN_1_in_data),
    .in_sel(sel_slice1_out),
    .out(muxN_1_out)
);
coreir_slice #(
    .hi(1),
    .lo(0),
    .width(2)
) sel_slice0 (
    .in(in_sel),
    .out(sel_slice0_out)
);
coreir_slice #(
    .hi(1),
    .lo(0),
    .width(2)
) sel_slice1 (
    .in(in_sel),
    .out(sel_slice1_out)
);
assign out = _join_out;
endmodule

module commonlib_muxn__N1__width32 (
    input [31:0] in_data [0:0],
    input [0:0] in_sel,
    output [31:0] out
);
corebit_term term_sel (
    .in(in_sel[0])
);
assign out = in_data[0];
endmodule

module commonlib_muxn__N5__width32 (
    input [31:0] in_data [4:0],
    input [2:0] in_sel,
    output [31:0] out
);
wire [31:0] _join_out;
wire [31:0] muxN_0_out;
wire [31:0] muxN_1_out;
wire [1:0] sel_slice0_out;
wire [0:0] sel_slice1_out;
coreir_mux #(
    .width(32)
) _join (
    .in0(muxN_0_out),
    .in1(muxN_1_out),
    .sel(in_sel[2]),
    .out(_join_out)
);
wire [31:0] muxN_0_in_data [3:0];
assign muxN_0_in_data[3] = in_data[3];
assign muxN_0_in_data[2] = in_data[2];
assign muxN_0_in_data[1] = in_data[1];
assign muxN_0_in_data[0] = in_data[0];
commonlib_muxn__N4__width32 muxN_0 (
    .in_data(muxN_0_in_data),
    .in_sel(sel_slice0_out),
    .out(muxN_0_out)
);
wire [31:0] muxN_1_in_data [0:0];
assign muxN_1_in_data[0] = in_data[4];
commonlib_muxn__N1__width32 muxN_1 (
    .in_data(muxN_1_in_data),
    .in_sel(sel_slice1_out),
    .out(muxN_1_out)
);
coreir_slice #(
    .hi(2),
    .lo(0),
    .width(3)
) sel_slice0 (
    .in(in_sel),
    .out(sel_slice0_out)
);
coreir_slice #(
    .hi(1),
    .lo(0),
    .width(3)
) sel_slice1 (
    .in(in_sel),
    .out(sel_slice1_out)
);
assign out = _join_out;
endmodule

module MuxWrapper_5_32 (
    input [31:0] I [4:0],
    output [31:0] O,
    input [2:0] S
);
wire [31:0] Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_out;
wire [31:0] Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data [4:0];
assign Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data[4] = I[4];
assign Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data[3] = I[3];
assign Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data[2] = I[2];
assign Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data[1] = I[1];
assign Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data[0] = I[0];
commonlib_muxn__N5__width32 Mux5x32_inst0$coreir_commonlib_mux5x32_inst0 (
    .in_data(Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data),
    .in_sel(S),
    .out(Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_out)
);
assign O = Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_out;
endmodule

