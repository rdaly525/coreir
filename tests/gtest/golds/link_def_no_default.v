// Module `STDCELLREG` defined externally
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

module foo_register (
    input [15:0] I,
    output [15:0] O,
    input CLK
);
coreir_reg #(
    .clk_posedge(1'b1),
    .init(16'h0000),
    .width(16)
) my_reg (
    .clk(CLK),
    .in(I),
    .out(O)
);
endmodule

module my_register_synthesis (
    input [15:0] I,
    output [15:0] O,
    input CLK
);
STDCELLREG stdcell_reg (
    .I(I),
    .O(O),
    .CLK(CLK)
);
endmodule

module my_register (
    input [15:0] I,
    output [15:0] O,
    input CLK
);
`ifdef SYNTHESIS
STDCELLREG stdcell_reg (
    .I(I),
    .O(O),
    .CLK(CLK)
);

`else
`ifdef FOO
coreir_reg #(
    .clk_posedge(1'b1),
    .init(16'h0000),
    .width(16)
) my_reg (
    .clk(CLK),
    .in(I),
    .out(O)
);

`endif
`endif
endmodule

