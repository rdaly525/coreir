module top (input MASK, input RADDR, input RCLK, input RCLKE, output RDATA, input RE, input WADDR, input WCLK, input WCLKE, input WDATA, input WE);
SB_RAM40_4K #(.INIT_0(256'h0000000000000000000000000000000000000000000000000000000000ff00fe), .INIT_1(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_2(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_3(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_4(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_5(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_6(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_7(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_8(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_9(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_A(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_B(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_C(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_D(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_E(256'h0000000000000000000000000000000000000000000000000000000000000000), .INIT_F(256'h0000000000000000000000000000000000000000000000000000000000000000), .READ_MODE(32'd0), .WRITE_MODE(32'd0)) SB_RAM40_4K_inst0(.MASK(MASK), .RADDR(RADDR), .RCLK(RCLK), .RCLKE(RCLKE), .RDATA(RDATA), .RE(RE), .WADDR(WADDR), .WCLK(WCLK), .WCLKE(WCLKE), .WDATA(WDATA), .WE(WE));
endmodule

