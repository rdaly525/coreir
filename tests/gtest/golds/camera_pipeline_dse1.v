module coreir_reg #(
    parameter width = 1,
    parameter clk_posedge = 1,
    parameter init = 1
) (
    input clk,
    input [width-1:0] in,
    output [width-1:0] out
);
  reg [width-1:0] outReg=init;
  wire real_clk;
  assign real_clk = clk_posedge ? clk : ~clk;
  always @(posedge real_clk) begin
    outReg <= in;
  end
  assign out = outReg;
endmodule

module mantle_reg__has_clrFalse__has_enTrue__has_rstFalse__width16 #(
    parameter init = 16'h0000
) (
    input [15:0] in,
    input clk,
    output [15:0] out,
    input en
);
wire [15:0] enMux_out;
assign enMux_out = en ? in : out;
coreir_reg #(
    .clk_posedge(1'b1),
    .init(init),
    .width(16)
) reg0 (
    .clk(clk),
    .in(enMux_out),
    .out(out)
);
endmodule

module coreir_mem #(
    parameter has_init = 1'b0,
    parameter sync_read = 1'b0,
    parameter depth = 1,
    parameter width = 1,
    parameter [(width * depth) - 1:0] init = 0
) (
    input clk,
    input [width-1:0] wdata,
    input [$clog2(depth)-1:0] waddr,
    input wen,
    output [width-1:0] rdata,
    input [$clog2(depth)-1:0] raddr
);
  reg [width-1:0] data [depth-1:0];
  generate if (has_init) begin
    genvar j;
    for (j = 0; j < depth; j = j + 1) begin
      initial begin
        data[j] = init[(j+1)*width-1:j*width];
      end
    end
  end
  endgenerate
  always @(posedge clk) begin
    if (wen) begin
      data[waddr] <= wdata;
    end
  end
  generate if (sync_read) begin
  reg [width-1:0] rdata_reg;
  always @(posedge clk) begin
    rdata_reg <= data[raddr];
  end
  assign rdata = rdata_reg;
  end else begin
  assign rdata = data[raddr];
  end
  endgenerate

endmodule

module memory_rom2__depth255__width16 #(
    parameter init = 1
) (
    input clk,
    output [15:0] rdata,
    input [15:0] raddr,
    input ren
);
wire [15:0] mem_rdata;
wire [15:0] wdata0_out;
coreir_mem #(
    .init(init),
    .depth(255),
    .has_init(1'b1),
    .sync_read(1'b0),
    .width(16)
) mem (
    .clk(clk),
    .wdata(wdata0_out),
    .waddr(8'h00),
    .wen(wdata0_out[0]),
    .rdata(mem_rdata),
    .raddr(raddr[8 - 1:0])
);
mantle_reg__has_clrFalse__has_enTrue__has_rstFalse__width16 #(
    .init(16'h0000)
) readreg (
    .in(mem_rdata),
    .clk(clk),
    .out(rdata),
    .en(ren)
);
assign wdata0_out = 16'h0000;
endmodule

module commonlib_smin__width16 (
    input [15:0] in0,
    input [15:0] in1,
    output [15:0] out
);
assign out = ($signed(in0)) <= ($signed(in1)) ? in0 : in1;
endmodule

module commonlib_smax__width16 (
    input [15:0] in0,
    input [15:0] in1,
    output [15:0] out
);
assign out = ($signed(in0)) >= ($signed(in1)) ? in0 : in1;
endmodule

module hcompute_hw_output_stencil (
    input clk,
    input [15:0] in0_f6_stencil_0,
    output [15:0] out_hw_output_stencil
);
wire [15:0] smax_1597_1598_1599_out;
wire [15:0] smin_f6_stencil_1_1596_1597_out;
memory_rom2__depth255__width16 #(
    .init({16'd63,16'd63,16'd62,16'd62,16'd62,16'd62,16'd61,16'd61,16'd61,16'd61,16'd60,16'd60,16'd60,16'd60,16'd59,16'd59,16'd59,16'd59,16'd58,16'd58,16'd58,16'd58,16'd57,16'd57,16'd57,16'd57,16'd56,16'd56,16'd56,16'd56,16'd55,16'd55,16'd55,16'd55,16'd54,16'd54,16'd54,16'd54,16'd53,16'd53,16'd53,16'd53,16'd52,16'd52,16'd52,16'd52,16'd51,16'd51,16'd51,16'd51,16'd50,16'd50,16'd50,16'd50,16'd49,16'd49,16'd49,16'd49,16'd48,16'd48,16'd48,16'd48,16'd47,16'd47,16'd47,16'd47,16'd46,16'd46,16'd46,16'd46,16'd45,16'd45,16'd45,16'd45,16'd44,16'd44,16'd44,16'd44,16'd43,16'd43,16'd43,16'd43,16'd42,16'd42,16'd42,16'd42,16'd41,16'd41,16'd41,16'd41,16'd40,16'd40,16'd40,16'd40,16'd39,16'd39,16'd39,16'd39,16'd38,16'd38,16'd38,16'd38,16'd37,16'd37,16'd37,16'd37,16'd36,16'd36,16'd36,16'd36,16'd35,16'd35,16'd35,16'd35,16'd34,16'd34,16'd34,16'd34,16'd33,16'd33,16'd33,16'd33,16'd32,16'd32,16'd32,16'd32,16'd31,16'd31,16'd31,16'd31,16'd30,16'd30,16'd30,16'd30,16'd29,16'd29,16'd29,16'd29,16'd28,16'd28,16'd28,16'd28,16'd27,16'd27,16'd27,16'd27,16'd26,16'd26,16'd26,16'd26,16'd25,16'd25,16'd25,16'd25,16'd24,16'd24,16'd24,16'd24,16'd23,16'd23,16'd23,16'd23,16'd22,16'd22,16'd22,16'd22,16'd21,16'd21,16'd21,16'd21,16'd20,16'd20,16'd20,16'd20,16'd19,16'd19,16'd19,16'd19,16'd18,16'd18,16'd18,16'd18,16'd17,16'd17,16'd17,16'd17,16'd16,16'd16,16'd16,16'd16,16'd15,16'd15,16'd15,16'd15,16'd14,16'd14,16'd14,16'd14,16'd13,16'd13,16'd13,16'd13,16'd12,16'd12,16'd12,16'd12,16'd11,16'd11,16'd11,16'd11,16'd10,16'd10,16'd10,16'd10,16'd9,16'd9,16'd9,16'd9,16'd8,16'd8,16'd8,16'd8,16'd7,16'd7,16'd7,16'd7,16'd6,16'd6,16'd6,16'd6,16'd5,16'd5,16'd5,16'd5,16'd4,16'd4,16'd4,16'd4,16'd3,16'd3,16'd3,16'd3,16'd2,16'd2,16'd2,16'd2,16'd1,16'd1,16'd1,16'd1,16'd0,16'd0,16'd0,16'd0,16'd0})
) curve$1 (
    .clk(clk),
    .rdata(out_hw_output_stencil),
    .raddr(smax_1597_1598_1599_out),
    .ren(1'b1)
);
commonlib_smax__width16 smax_1597_1598_1599 (
    .in0(smin_f6_stencil_1_1596_1597_out),
    .in1(16'h0000),
    .out(smax_1597_1598_1599_out)
);
commonlib_smin__width16 smin_f6_stencil_1_1596_1597 (
    .in0(in0_f6_stencil_0),
    .in1(16'h03ff),
    .out(smin_f6_stencil_1_1596_1597_out)
);
endmodule

