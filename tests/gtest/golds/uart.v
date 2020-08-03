module coreir_reg_arst #(
    parameter width = 1,
    parameter arst_posedge = 1,
    parameter clk_posedge = 1,
    parameter init = 1
) (
    input clk,
    input arst,
    input [width-1:0] in,
    output [width-1:0] out
);
  reg [width-1:0] outReg;
  wire real_rst;
  assign real_rst = arst_posedge ? arst : ~arst;
  wire real_clk;
  assign real_clk = clk_posedge ? clk : ~clk;
  always @(posedge real_clk, posedge real_rst) begin
    if (real_rst) outReg <= init;
    else outReg <= in;
  end
  assign out = outReg;
endmodule

module UART_comb (
    input run,
    input [7:0] message,
    input [7:0] self_message_O,
    input [2:0] self_i_O,
    input self_tx_O,
    input [1:0] self_yield_state_O,
    output [7:0] O0,
    output [2:0] O1,
    output O2,
    output [1:0] O3,
    output O4
);
reg [0:0] Mux2xOutBit_inst0$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst1$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst10$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst11$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst2$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst3$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst4$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst5$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst6$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst7$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst8$coreir_commonlib_mux2x1_inst0_out;
reg [0:0] Mux2xOutBit_inst9$coreir_commonlib_mux2x1_inst0_out;
reg [1:0] Mux2xOutBits2_inst0$coreir_commonlib_mux2x2_inst0_out;
reg [1:0] Mux2xOutBits2_inst1$coreir_commonlib_mux2x2_inst0_out;
reg [1:0] Mux2xOutBits2_inst2$coreir_commonlib_mux2x2_inst0_out;
reg [1:0] Mux2xOutBits2_inst3$coreir_commonlib_mux2x2_inst0_out;
reg [1:0] Mux2xOutBits2_inst4$coreir_commonlib_mux2x2_inst0_out;
reg [1:0] Mux2xOutBits2_inst5$coreir_commonlib_mux2x2_inst0_out;
reg [1:0] Mux2xOutBits2_inst6$coreir_commonlib_mux2x2_inst0_out;
reg [1:0] Mux2xOutBits2_inst7$coreir_commonlib_mux2x2_inst0_out;
reg [7:0] Mux2xOutBits8_inst0$coreir_commonlib_mux2x8_inst0_out;
reg [7:0] Mux2xOutBits8_inst1$coreir_commonlib_mux2x8_inst0_out;
reg [7:0] Mux2xOutBits8_inst2$coreir_commonlib_mux2x8_inst0_out;
reg [7:0] Mux2xOutBits8_inst3$coreir_commonlib_mux2x8_inst0_out;
reg [7:0] Mux2xOutBits8_inst4$coreir_commonlib_mux2x8_inst0_out;
reg [7:0] Mux2xOutBits8_inst5$coreir_commonlib_mux2x8_inst0_out;
reg [2:0] Mux2xOutUInt3_inst0$coreir_commonlib_mux2x3_inst0_out;
reg [2:0] Mux2xOutUInt3_inst1$coreir_commonlib_mux2x3_inst0_out;
reg [2:0] Mux2xOutUInt3_inst2$coreir_commonlib_mux2x3_inst0_out;
reg [2:0] Mux2xOutUInt3_inst3$coreir_commonlib_mux2x3_inst0_out;
reg [2:0] Mux2xOutUInt3_inst4$coreir_commonlib_mux2x3_inst0_out;
reg [2:0] Mux2xOutUInt3_inst5$coreir_commonlib_mux2x3_inst0_out;
reg [2:0] Mux2xOutUInt3_inst6$coreir_commonlib_mux2x3_inst0_out;
wire [2:0] magma_Bits_3_sub_inst0_out;
wire [2:0] magma_Bits_3_sub_inst1_out;
wire [7:0] magma_Bits_8_lshr_inst0_out;
wire [7:0] magma_Bits_8_lshr_inst1_out;
always @(*) begin
if (run == 0) begin
    Mux2xOutBit_inst0$coreir_commonlib_mux2x1_inst0_out = 1'b1;
end else begin
    Mux2xOutBit_inst0$coreir_commonlib_mux2x1_inst0_out = 1'b0;
end
if ((~ (self_i_O == 3'h7)) == 0) begin
    Mux2xOutBit_inst1$coreir_commonlib_mux2x1_inst0_out = 1'b1;
end else begin
    Mux2xOutBit_inst1$coreir_commonlib_mux2x1_inst0_out = magma_Bits_8_lshr_inst1_out[0];
end
if ((run & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBit_inst10$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst8$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst10$coreir_commonlib_mux2x1_inst0_out = 1'b0;
end
if ((run & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBit_inst11$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst9$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst11$coreir_commonlib_mux2x1_inst0_out = self_tx_O;
end
if ((self_yield_state_O == 2'h1) == 0) begin
    Mux2xOutBit_inst2$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst1$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst2$coreir_commonlib_mux2x1_inst0_out = magma_Bits_8_lshr_inst0_out[0];
end
if ((self_yield_state_O == 2'h0) == 0) begin
    Mux2xOutBit_inst3$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst2$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst3$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst0$coreir_commonlib_mux2x1_inst0_out[0];
end
if ((((~ (self_i_O == 3'h7)) & (~ (self_yield_state_O == 2'h0))) & (~ (self_yield_state_O == 2'h1))) == 0) begin
    Mux2xOutBit_inst4$coreir_commonlib_mux2x1_inst0_out = 1'b1;
end else begin
    Mux2xOutBit_inst4$coreir_commonlib_mux2x1_inst0_out = magma_Bits_8_lshr_inst1_out[0];
end
if ((((~ (self_i_O == 3'h7)) & (~ (self_yield_state_O == 2'h0))) & (~ (self_yield_state_O == 2'h1))) == 0) begin
    Mux2xOutBit_inst5$coreir_commonlib_mux2x1_inst0_out = self_tx_O;
end else begin
    Mux2xOutBit_inst5$coreir_commonlib_mux2x1_inst0_out = self_tx_O;
end
if (((self_yield_state_O == 2'h1) & (~ (self_yield_state_O == 2'h0))) == 0) begin
    Mux2xOutBit_inst6$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst4$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst6$coreir_commonlib_mux2x1_inst0_out = magma_Bits_8_lshr_inst0_out[0];
end
if (((self_yield_state_O == 2'h1) & (~ (self_yield_state_O == 2'h0))) == 0) begin
    Mux2xOutBit_inst7$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst5$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst7$coreir_commonlib_mux2x1_inst0_out = self_tx_O;
end
if (((~ run) & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBit_inst8$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst6$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst8$coreir_commonlib_mux2x1_inst0_out = 1'b1;
end
if (((~ run) & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBit_inst9$coreir_commonlib_mux2x1_inst0_out = Mux2xOutBit_inst7$coreir_commonlib_mux2x1_inst0_out[0];
end else begin
    Mux2xOutBit_inst9$coreir_commonlib_mux2x1_inst0_out = self_tx_O;
end
if (run == 0) begin
    Mux2xOutBits2_inst0$coreir_commonlib_mux2x2_inst0_out = 2'h0;
end else begin
    Mux2xOutBits2_inst0$coreir_commonlib_mux2x2_inst0_out = 2'h1;
end
if ((~ (self_i_O == 3'h7)) == 0) begin
    Mux2xOutBits2_inst1$coreir_commonlib_mux2x2_inst0_out = 2'h0;
end else begin
    Mux2xOutBits2_inst1$coreir_commonlib_mux2x2_inst0_out = 2'h2;
end
if ((self_yield_state_O == 2'h1) == 0) begin
    Mux2xOutBits2_inst2$coreir_commonlib_mux2x2_inst0_out = Mux2xOutBits2_inst1$coreir_commonlib_mux2x2_inst0_out;
end else begin
    Mux2xOutBits2_inst2$coreir_commonlib_mux2x2_inst0_out = 2'h2;
end
if ((self_yield_state_O == 2'h0) == 0) begin
    Mux2xOutBits2_inst3$coreir_commonlib_mux2x2_inst0_out = Mux2xOutBits2_inst2$coreir_commonlib_mux2x2_inst0_out;
end else begin
    Mux2xOutBits2_inst3$coreir_commonlib_mux2x2_inst0_out = Mux2xOutBits2_inst0$coreir_commonlib_mux2x2_inst0_out;
end
if ((((~ (self_i_O == 3'h7)) & (~ (self_yield_state_O == 2'h0))) & (~ (self_yield_state_O == 2'h1))) == 0) begin
    Mux2xOutBits2_inst4$coreir_commonlib_mux2x2_inst0_out = 2'h0;
end else begin
    Mux2xOutBits2_inst4$coreir_commonlib_mux2x2_inst0_out = 2'h2;
end
if (((self_yield_state_O == 2'h1) & (~ (self_yield_state_O == 2'h0))) == 0) begin
    Mux2xOutBits2_inst5$coreir_commonlib_mux2x2_inst0_out = Mux2xOutBits2_inst4$coreir_commonlib_mux2x2_inst0_out;
end else begin
    Mux2xOutBits2_inst5$coreir_commonlib_mux2x2_inst0_out = 2'h2;
end
if (((~ run) & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBits2_inst6$coreir_commonlib_mux2x2_inst0_out = Mux2xOutBits2_inst5$coreir_commonlib_mux2x2_inst0_out;
end else begin
    Mux2xOutBits2_inst6$coreir_commonlib_mux2x2_inst0_out = 2'h0;
end
if ((run & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBits2_inst7$coreir_commonlib_mux2x2_inst0_out = Mux2xOutBits2_inst6$coreir_commonlib_mux2x2_inst0_out;
end else begin
    Mux2xOutBits2_inst7$coreir_commonlib_mux2x2_inst0_out = 2'h1;
end
if (run == 0) begin
    Mux2xOutBits8_inst0$coreir_commonlib_mux2x8_inst0_out = self_message_O;
end else begin
    Mux2xOutBits8_inst0$coreir_commonlib_mux2x8_inst0_out = message;
end
if ((self_yield_state_O == 2'h0) == 0) begin
    Mux2xOutBits8_inst1$coreir_commonlib_mux2x8_inst0_out = self_message_O;
end else begin
    Mux2xOutBits8_inst1$coreir_commonlib_mux2x8_inst0_out = Mux2xOutBits8_inst0$coreir_commonlib_mux2x8_inst0_out;
end
if ((((~ (self_i_O == 3'h7)) & (~ (self_yield_state_O == 2'h0))) & (~ (self_yield_state_O == 2'h1))) == 0) begin
    Mux2xOutBits8_inst2$coreir_commonlib_mux2x8_inst0_out = self_message_O;
end else begin
    Mux2xOutBits8_inst2$coreir_commonlib_mux2x8_inst0_out = self_message_O;
end
if (((self_yield_state_O == 2'h1) & (~ (self_yield_state_O == 2'h0))) == 0) begin
    Mux2xOutBits8_inst3$coreir_commonlib_mux2x8_inst0_out = Mux2xOutBits8_inst2$coreir_commonlib_mux2x8_inst0_out;
end else begin
    Mux2xOutBits8_inst3$coreir_commonlib_mux2x8_inst0_out = self_message_O;
end
if (((~ run) & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBits8_inst4$coreir_commonlib_mux2x8_inst0_out = Mux2xOutBits8_inst3$coreir_commonlib_mux2x8_inst0_out;
end else begin
    Mux2xOutBits8_inst4$coreir_commonlib_mux2x8_inst0_out = self_message_O;
end
if ((run & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutBits8_inst5$coreir_commonlib_mux2x8_inst0_out = Mux2xOutBits8_inst4$coreir_commonlib_mux2x8_inst0_out;
end else begin
    Mux2xOutBits8_inst5$coreir_commonlib_mux2x8_inst0_out = message;
end
if ((~ (self_i_O == 3'h7)) == 0) begin
    Mux2xOutUInt3_inst0$coreir_commonlib_mux2x3_inst0_out = self_i_O;
end else begin
    Mux2xOutUInt3_inst0$coreir_commonlib_mux2x3_inst0_out = magma_Bits_3_sub_inst1_out;
end
if ((self_yield_state_O == 2'h1) == 0) begin
    Mux2xOutUInt3_inst1$coreir_commonlib_mux2x3_inst0_out = Mux2xOutUInt3_inst0$coreir_commonlib_mux2x3_inst0_out;
end else begin
    Mux2xOutUInt3_inst1$coreir_commonlib_mux2x3_inst0_out = magma_Bits_3_sub_inst0_out;
end
if ((self_yield_state_O == 2'h0) == 0) begin
    Mux2xOutUInt3_inst2$coreir_commonlib_mux2x3_inst0_out = Mux2xOutUInt3_inst1$coreir_commonlib_mux2x3_inst0_out;
end else begin
    Mux2xOutUInt3_inst2$coreir_commonlib_mux2x3_inst0_out = self_i_O;
end
if ((((~ (self_i_O == 3'h7)) & (~ (self_yield_state_O == 2'h0))) & (~ (self_yield_state_O == 2'h1))) == 0) begin
    Mux2xOutUInt3_inst3$coreir_commonlib_mux2x3_inst0_out = self_i_O;
end else begin
    Mux2xOutUInt3_inst3$coreir_commonlib_mux2x3_inst0_out = magma_Bits_3_sub_inst1_out;
end
if (((self_yield_state_O == 2'h1) & (~ (self_yield_state_O == 2'h0))) == 0) begin
    Mux2xOutUInt3_inst4$coreir_commonlib_mux2x3_inst0_out = Mux2xOutUInt3_inst3$coreir_commonlib_mux2x3_inst0_out;
end else begin
    Mux2xOutUInt3_inst4$coreir_commonlib_mux2x3_inst0_out = magma_Bits_3_sub_inst0_out;
end
if (((~ run) & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutUInt3_inst5$coreir_commonlib_mux2x3_inst0_out = Mux2xOutUInt3_inst4$coreir_commonlib_mux2x3_inst0_out;
end else begin
    Mux2xOutUInt3_inst5$coreir_commonlib_mux2x3_inst0_out = self_i_O;
end
if ((run & (self_yield_state_O == 2'h0)) == 0) begin
    Mux2xOutUInt3_inst6$coreir_commonlib_mux2x3_inst0_out = Mux2xOutUInt3_inst5$coreir_commonlib_mux2x3_inst0_out;
end else begin
    Mux2xOutUInt3_inst6$coreir_commonlib_mux2x3_inst0_out = self_i_O;
end
end

assign magma_Bits_3_sub_inst0_out = 3'(self_i_O - 3'h1);
assign magma_Bits_3_sub_inst1_out = 3'(self_i_O - 3'h1);
assign magma_Bits_8_lshr_inst0_out = self_message_O >> ({1'b0,1'b0,1'b0,1'b0,1'b0,self_i_O[2],self_i_O[1],self_i_O[0]});
assign magma_Bits_8_lshr_inst1_out = self_message_O >> ({1'b0,1'b0,1'b0,1'b0,1'b0,self_i_O[2],self_i_O[1],self_i_O[0]});
assign O0 = Mux2xOutBits8_inst5$coreir_commonlib_mux2x8_inst0_out;
assign O1 = Mux2xOutUInt3_inst6$coreir_commonlib_mux2x3_inst0_out;
assign O2 = Mux2xOutBit_inst10$coreir_commonlib_mux2x1_inst0_out[0];
assign O3 = Mux2xOutBits2_inst7$coreir_commonlib_mux2x2_inst0_out;
assign O4 = Mux2xOutBit_inst11$coreir_commonlib_mux2x1_inst0_out[0];
endmodule

module UART (
    input run,
    input [7:0] message,
    input CLK,
    input ASYNCRESET,
    output O
);
wire DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_clk;
wire DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_arst;
wire [0:0] DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_in;
wire [0:0] DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_out;
wire UART_comb_inst0_run;
wire [7:0] UART_comb_inst0_message;
wire [7:0] UART_comb_inst0_self_message_O;
wire [2:0] UART_comb_inst0_self_i_O;
wire UART_comb_inst0_self_tx_O;
wire [1:0] UART_comb_inst0_self_yield_state_O;
wire [7:0] UART_comb_inst0_O0;
wire [2:0] UART_comb_inst0_O1;
wire UART_comb_inst0_O2;
wire [1:0] UART_comb_inst0_O3;
wire reg_PR_inst0_clk;
wire reg_PR_inst0_arst;
wire [7:0] reg_PR_inst0_in;
wire [7:0] reg_PR_inst0_out;
wire reg_PR_inst1_clk;
wire reg_PR_inst1_arst;
wire [2:0] reg_PR_inst1_in;
wire [2:0] reg_PR_inst1_out;
wire reg_PR_inst2_clk;
wire reg_PR_inst2_arst;
wire [1:0] reg_PR_inst2_in;
wire [1:0] reg_PR_inst2_out;
assign DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_clk = CLK;
assign DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_arst = ASYNCRESET;
assign DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_in = UART_comb_inst0_O2;
coreir_reg_arst #(
    .arst_posedge(1'b1),
    .clk_posedge(1'b1),
    .init(1'h1),
    .width(1)
) DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0 (
    .clk(DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_clk),
    .arst(DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_arst),
    .in(DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_in),
    .out(DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_out)
);
assign UART_comb_inst0_run = run;
assign UART_comb_inst0_message = message;
assign UART_comb_inst0_self_message_O = reg_PR_inst0_out;
assign UART_comb_inst0_self_i_O = reg_PR_inst1_out;
assign UART_comb_inst0_self_tx_O = DFF_initTrue_has_ceFalse_has_resetFalse_has_async_resetTrue_inst0$reg_PR_inst0_out[0];
assign UART_comb_inst0_self_yield_state_O = reg_PR_inst2_out;
UART_comb UART_comb_inst0 (
    .run(UART_comb_inst0_run),
    .message(UART_comb_inst0_message),
    .self_message_O(UART_comb_inst0_self_message_O),
    .self_i_O(UART_comb_inst0_self_i_O),
    .self_tx_O(UART_comb_inst0_self_tx_O),
    .self_yield_state_O(UART_comb_inst0_self_yield_state_O),
    .O0(UART_comb_inst0_O0),
    .O1(UART_comb_inst0_O1),
    .O2(UART_comb_inst0_O2),
    .O3(UART_comb_inst0_O3),
    .O4(O)
);
assign reg_PR_inst0_clk = CLK;
assign reg_PR_inst0_arst = ASYNCRESET;
assign reg_PR_inst0_in = UART_comb_inst0_O0;
coreir_reg_arst #(
    .arst_posedge(1'b1),
    .clk_posedge(1'b1),
    .init(8'h00),
    .width(8)
) reg_PR_inst0 (
    .clk(reg_PR_inst0_clk),
    .arst(reg_PR_inst0_arst),
    .in(reg_PR_inst0_in),
    .out(reg_PR_inst0_out)
);
assign reg_PR_inst1_clk = CLK;
assign reg_PR_inst1_arst = ASYNCRESET;
assign reg_PR_inst1_in = UART_comb_inst0_O1;
coreir_reg_arst #(
    .arst_posedge(1'b1),
    .clk_posedge(1'b1),
    .init(3'h7),
    .width(3)
) reg_PR_inst1 (
    .clk(reg_PR_inst1_clk),
    .arst(reg_PR_inst1_arst),
    .in(reg_PR_inst1_in),
    .out(reg_PR_inst1_out)
);
assign reg_PR_inst2_clk = CLK;
assign reg_PR_inst2_arst = ASYNCRESET;
assign reg_PR_inst2_in = UART_comb_inst0_O3;
coreir_reg_arst #(
    .arst_posedge(1'b1),
    .clk_posedge(1'b1),
    .init(2'h0),
    .width(2)
) reg_PR_inst2 (
    .clk(reg_PR_inst2_clk),
    .arst(reg_PR_inst2_arst),
    .in(reg_PR_inst2_in),
    .out(reg_PR_inst2_out)
);
endmodule

