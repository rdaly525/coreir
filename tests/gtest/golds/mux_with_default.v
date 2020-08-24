
module MuxWithDefaultWrapper_9_32_8_0 (
    input [31:0] I [8:0],
    input [7:0] S,
    input [0:0] EN,
    output [31:0] O
);
reg [31:0] MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out;
always @(*) begin
if (S[3:0] == 0) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[0];
end else if (S[3:0] == 1) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[1];
end else if (S[3:0] == 2) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[2];
end else if (S[3:0] == 3) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[3];
end else if (S[3:0] == 4) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[4];
end else if (S[3:0] == 5) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[5];
end else if (S[3:0] == 6) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[6];
end else if (S[3:0] == 7) begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[7];
end else begin
    MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out = I[8];
end
end

assign O = (S < 8'h09) & EN[0] ? MuxWrapper_9_32_inst0$Mux9x32_inst0$coreir_commonlib_mux9x32_inst0_out : 32'h00000000;
endmodule

