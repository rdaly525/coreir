module coreir_mem #(
    parameter has_init = 1'b0,
    parameter sync_read = 1'b0,
    parameter depth = 1,
    parameter width = 1
) (
    input clk,
    input [width-1:0] wdata,
    input [$clog2(depth)-1:0] waddr,
    input wen,
    output [width-1:0] rdata,
    input [$clog2(depth)-1:0] raddr
);
  reg [width-1:0] data [depth-1:0];
  parameter [width*depth-1:0] init = 0;
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

module Memory (
    input [1:0] RADDR,
    output [4:0] RDATA,
    input CLK
);
wire coreir_mem4x5_inst0_clk;
wire [4:0] coreir_mem4x5_inst0_wdata;
wire [1:0] coreir_mem4x5_inst0_waddr;
wire coreir_mem4x5_inst0_wen;
wire [1:0] coreir_mem4x5_inst0_raddr;
assign coreir_mem4x5_inst0_clk = CLK;
assign coreir_mem4x5_inst0_wdata = 5'h00;
assign coreir_mem4x5_inst0_waddr = 2'h0;
assign coreir_mem4x5_inst0_wen = 1'b0;
assign coreir_mem4x5_inst0_raddr = RADDR;
coreir_mem #(
    .init({5'd11,5'd21,5'd0,5'd5}),
    .depth(4),
    .has_init(1'b1),
    .sync_read(1'b0),
    .width(5)
) coreir_mem4x5_inst0 (
    .clk(coreir_mem4x5_inst0_clk),
    .wdata(coreir_mem4x5_inst0_wdata),
    .waddr(coreir_mem4x5_inst0_waddr),
    .wen(coreir_mem4x5_inst0_wen),
    .rdata(RDATA),
    .raddr(coreir_mem4x5_inst0_raddr)
);
endmodule

module test_memory_read_only (
    input [1:0] raddr,
    output [4:0] rdata,
    input clk
);
wire [1:0] Memory_inst0_RADDR;
wire Memory_inst0_CLK;
assign Memory_inst0_RADDR = raddr;
assign Memory_inst0_CLK = clk;
Memory Memory_inst0 (
    .RADDR(Memory_inst0_RADDR),
    .RDATA(rdata),
    .CLK(Memory_inst0_CLK)
);
endmodule

