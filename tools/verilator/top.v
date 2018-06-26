

module wire_U0 (
  input [15:0] in,
  output [15:0] out
);
  //All the connections
  assign out[15:0] = in[15:0];

endmodule //wire_U0

module corebit_const #(parameter value=1) (
  output out
);
  assign out = value;

endmodule //corebit_const

module coreir_add #(parameter width=1) (
  input [width-1:0] in0,
  input [width-1:0] in1,
  output [width-1:0] out
);
  assign out = in0 + in1;

endmodule //coreir_add

module coreir_const #(parameter value=1, parameter width=1) (
  output [width-1:0] out
);
  assign out = value;

endmodule //coreir_const

module coreir_reg #(parameter init=1, parameter width=1) (
  input clk,
  input [width-1:0] in,
  output [width-1:0] out
);
reg [width-1:0] outReg=init;
always @(posedge clk) begin
  outReg <= in;
end
assign out = outReg;

endmodule //coreir_reg

module Linebuffer_U3 (
  input  clk,
  input [15:0] in,
  output [15:0] out_0_0,
  output [15:0] out_0_1,
  input  wen
);
  //Wire declarations for instance 'reg_0_1' (Module coreir_reg)
  wire  reg_0_1__clk;
  wire [15:0] reg_0_1__in;
  wire [15:0] reg_0_1__out;
  coreir_reg #(.init(16'd0),.width(16)) reg_0_1(
    .clk(reg_0_1__clk),
    .in(reg_0_1__in),
    .out(reg_0_1__out)
  );

  //All the connections
  assign reg_0_1__clk = clk;
  assign reg_0_1__in[15:0] = in[15:0];
  assign out_0_0[15:0] = reg_0_1__out[15:0];
  assign out_0_1[15:0] = in[15:0];

endmodule //Linebuffer_U3

module DesignTop (
  input  clk,
  input [15:0] in_0,
  output [15:0] out,
  output [15:0] lb0,
  output [15:0] lb1
);
  //Wire declarations for instance '_302_pt' (Module wire_U0)
  wire [15:0] _302_pt__in;
  wire [15:0] _302_pt__out;
  wire_U0 _302_pt(
    .in(_302_pt__in),
    .out(_302_pt__out)
  );

  //Wire declarations for instance '_305_pt' (Module wire_U0)
  wire [15:0] _305_pt__in;
  wire [15:0] _305_pt__out;
  wire_U0 _305_pt(
    .in(_305_pt__in),
    .out(_305_pt__out)
  );

  //Wire declarations for instance 'add_301_303_304' (Module coreir_add)
  wire [15:0] add_301_303_304__in0;
  wire [15:0] add_301_303_304__out;
  wire [15:0] add_301_303_304__in1;
  coreir_add #(.width(16)) add_301_303_304(
    .in0(add_301_303_304__in0),
    .in1(add_301_303_304__in1),
    .out(add_301_303_304__out)
  );

  //Wire declarations for instance 'add_301_306_307' (Module coreir_add)
  wire [15:0] add_301_306_307__in0;
  wire [15:0] add_301_306_307__out;
  wire [15:0] add_301_306_307__in1;
  coreir_add #(.width(16)) add_301_306_307(
    .in0(add_301_306_307__in0),
    .in1(add_301_306_307__in1),
    .out(add_301_306_307__out)
  );

  //Wire declarations for instance 'const0__300' (Module coreir_const)
  wire [15:0] const0__300__out;
  coreir_const #(.value(16'd0),.width(16)) const0__300(
    .out(const0__300__out)
  );

  //Wire declarations for instance 'lb_p4_clamped_stencil_update_stream' (Module Linebuffer_U3)
  wire  lb_p4_clamped_stencil_update_stream__wen;
  wire [15:0] lb_p4_clamped_stencil_update_stream__out_0_1;
  wire  lb_p4_clamped_stencil_update_stream__clk;
  wire [15:0] lb_p4_clamped_stencil_update_stream__out_0_0;
  wire [15:0] lb_p4_clamped_stencil_update_stream__in;
  Linebuffer_U3 lb_p4_clamped_stencil_update_stream(
    .clk(lb_p4_clamped_stencil_update_stream__clk),
    .in(lb_p4_clamped_stencil_update_stream__in),
    .out_0_0(lb_p4_clamped_stencil_update_stream__out_0_0),
    .out_0_1(lb_p4_clamped_stencil_update_stream__out_0_1),
    .wen(lb_p4_clamped_stencil_update_stream__wen)
  );
  assign lb0 = lb_p4_clamped_stencil_update_stream__out_0_0;
  assign lb1 = lb_p4_clamped_stencil_update_stream__out_0_1;
  //Wire declarations for instance 'lb_p4_clamped_stencil_update_stream_wen' (Module corebit_const)
  wire  lb_p4_clamped_stencil_update_stream_wen__out;
  corebit_const #(.value(1)) lb_p4_clamped_stencil_update_stream_wen(
    .out(lb_p4_clamped_stencil_update_stream_wen__out)
  );

  //All the connections
  assign _302_pt__in[15:0] = lb_p4_clamped_stencil_update_stream__out_0_0[15:0];
  assign add_301_303_304__in1[15:0] = _302_pt__out[15:0];
  assign _305_pt__in[15:0] = lb_p4_clamped_stencil_update_stream__out_0_1[15:0];
  assign add_301_306_307__in1[15:0] = _305_pt__out[15:0];
  assign add_301_303_304__in0[15:0] = const0__300__out[15:0];
  assign add_301_306_307__in0[15:0] = add_301_303_304__out[15:0];
  assign out[15:0] = add_301_306_307__out[15:0];
  assign lb_p4_clamped_stencil_update_stream__clk = clk;
  assign lb_p4_clamped_stencil_update_stream__in[15:0] = in_0[15:0];
  assign lb_p4_clamped_stencil_update_stream__wen = lb_p4_clamped_stencil_update_stream_wen__out;

endmodule //DesignTop
