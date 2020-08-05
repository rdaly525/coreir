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
wire [31:0] _join_in0;
wire [31:0] _join_in1;
wire _join_sel;
wire [31:0] _join_out;
assign _join_in0 = in_data[0];
assign _join_in1 = in_data[1];
assign _join_sel = in_sel[0];
coreir_mux #(
    .width(32)
) _join (
    .in0(_join_in0),
    .in1(_join_in1),
    .sel(_join_sel),
    .out(_join_out)
);
assign out = _join_out;
endmodule

module commonlib_muxn__N4__width32 (
    input [31:0] in_data [3:0],
    input [1:0] in_sel,
    output [31:0] out
);
wire [31:0] _join_in0;
wire [31:0] _join_in1;
wire _join_sel;
wire [31:0] _join_out;
wire [31:0] muxN_0_in_data [1:0];
wire [0:0] muxN_0_in_sel;
wire [31:0] muxN_0_out;
wire [31:0] muxN_1_in_data [1:0];
wire [0:0] muxN_1_in_sel;
wire [31:0] muxN_1_out;
wire [1:0] sel_slice0_in;
wire [0:0] sel_slice0_out;
wire [1:0] sel_slice1_in;
wire [0:0] sel_slice1_out;
assign _join_in0 = muxN_0_out;
assign _join_in1 = muxN_1_out;
assign _join_sel = in_sel[1];
coreir_mux #(
    .width(32)
) _join (
    .in0(_join_in0),
    .in1(_join_in1),
    .sel(_join_sel),
    .out(_join_out)
);
assign muxN_0_in_data = '{in_data[0],in_data[1]};
assign muxN_0_in_sel = sel_slice0_out;
commonlib_muxn__N2__width32 muxN_0 (
    .in_data(muxN_0_in_data),
    .in_sel(muxN_0_in_sel),
    .out(muxN_0_out)
);
assign muxN_1_in_data = '{in_data[2],in_data[3]};
assign muxN_1_in_sel = sel_slice1_out;
commonlib_muxn__N2__width32 muxN_1 (
    .in_data(muxN_1_in_data),
    .in_sel(muxN_1_in_sel),
    .out(muxN_1_out)
);
assign sel_slice0_in = in_sel;
coreir_slice #(
    .hi(1),
    .lo(0),
    .width(2)
) sel_slice0 (
    .in(sel_slice0_in),
    .out(sel_slice0_out)
);
assign sel_slice1_in = in_sel;
coreir_slice #(
    .hi(1),
    .lo(0),
    .width(2)
) sel_slice1 (
    .in(sel_slice1_in),
    .out(sel_slice1_out)
);
assign out = _join_out;
endmodule

module commonlib_muxn__N1__width32 (
    input [31:0] in_data [0:0],
    input [0:0] in_sel,
    output [31:0] out
);
wire term_sel_in;
assign term_sel_in = in_sel[0];
corebit_term term_sel (
    .in(term_sel_in)
);
assign out = in_data[0];
endmodule

module commonlib_muxn__N5__width32 (
    input [31:0] in_data [4:0],
    input [2:0] in_sel,
    output [31:0] out
);
wire [31:0] _join_in0;
wire [31:0] _join_in1;
wire _join_sel;
wire [31:0] _join_out;
wire [31:0] muxN_0_in_data [3:0];
wire [1:0] muxN_0_in_sel;
wire [31:0] muxN_0_out;
wire [31:0] muxN_1_in_data [0:0];
wire [0:0] muxN_1_in_sel;
wire [31:0] muxN_1_out;
wire [2:0] sel_slice0_in;
wire [1:0] sel_slice0_out;
wire [2:0] sel_slice1_in;
wire [0:0] sel_slice1_out;
assign _join_in0 = muxN_0_out;
assign _join_in1 = muxN_1_out;
assign _join_sel = in_sel[2];
coreir_mux #(
    .width(32)
) _join (
    .in0(_join_in0),
    .in1(_join_in1),
    .sel(_join_sel),
    .out(_join_out)
);
assign muxN_0_in_data = '{in_data[0],in_data[1],in_data[2],in_data[3]};
assign muxN_0_in_sel = sel_slice0_out;
commonlib_muxn__N4__width32 muxN_0 (
    .in_data(muxN_0_in_data),
    .in_sel(muxN_0_in_sel),
    .out(muxN_0_out)
);
assign muxN_1_in_data[0] = in_data[4];
assign muxN_1_in_sel = sel_slice1_out;
commonlib_muxn__N1__width32 muxN_1 (
    .in_data(muxN_1_in_data),
    .in_sel(muxN_1_in_sel),
    .out(muxN_1_out)
);
assign sel_slice0_in = in_sel;
coreir_slice #(
    .hi(2),
    .lo(0),
    .width(3)
) sel_slice0 (
    .in(sel_slice0_in),
    .out(sel_slice0_out)
);
assign sel_slice1_in = in_sel;
coreir_slice #(
    .hi(1),
    .lo(0),
    .width(3)
) sel_slice1 (
    .in(sel_slice1_in),
    .out(sel_slice1_out)
);
assign out = _join_out;
endmodule

module MuxWrapper_5_32 (
    input [31:0] I [4:0],
    output [31:0] O,
    input [2:0] S
);
wire [31:0] Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data [4:0];
wire [2:0] Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_sel;
wire [31:0] Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_out;
assign Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data = '{I[0],I[1],I[2],I[3],I[4]};
assign Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_sel = S;
commonlib_muxn__N5__width32 Mux5x32_inst0$coreir_commonlib_mux5x32_inst0 (
    .in_data(Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_data),
    .in_sel(Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_in_sel),
    .out(Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_out)
);
assign O = Mux5x32_inst0$coreir_commonlib_mux5x32_inst0_out;
endmodule

