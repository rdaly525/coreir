module VerilogReg (input [9:0] I, output [9:0] O, input CE, input AsyncResetN, input   CLK);
  reg [9:0] R;
  always @ (posedge CLK or negedge AsyncResetN) begin
    if (AsyncResetN == 1'b0) begin
      R <= 10'd0;
    end else begin
      if (CE == 1'b1)
          R <= I;
    end
  end
  assign O = R;
endmodule
module Register (
    input AsyncResetN,
    input CE,
    input CLK,
    input [7:0] I_address [0:0],
    input [0:0] I_addressValid,
    input I_valid,
    output [7:0] O_address [0:0],
    output [0:0] O_addressValid,
    output O_valid
);
wire [9:0] v_reg_O;
wire [9:0] v_reg_I;
assign v_reg_I = {I_address[0][7:0],I_addressValid[0],I_valid};
VerilogReg v_reg (
    .I(v_reg_I),
    .O(v_reg_O),
    .CE(CE),
    .AsyncResetN(AsyncResetN),
    .CLK(CLK)
);
assign O_address[0] = v_reg_O[9:2];
assign O_addressValid = v_reg_O[1];
assign O_valid = v_reg_O[0];
endmodule

