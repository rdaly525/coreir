module Mux2xArray3_Array2_OutBit (
    input [1:0] I0 [2:0],
    input [1:0] I1 [2:0],
    input S,
    output [1:0] O [2:0]
);
reg [5:0] coreir_commonlib_mux2x6_inst0_out_unq1;
always @(*) begin
if (S == 0) begin
    coreir_commonlib_mux2x6_inst0_out_unq1 = {I0[2][1:0],I0[1][1:0],I0[0][1:0]};
end else begin
    coreir_commonlib_mux2x6_inst0_out_unq1 = {I1[2][1:0],I1[1][1:0],I1[0][1:0]};
end
end

assign O[2] = coreir_commonlib_mux2x6_inst0_out_unq1[5:4];
assign O[1] = coreir_commonlib_mux2x6_inst0_out_unq1[3:2];
assign O[0] = coreir_commonlib_mux2x6_inst0_out_unq1[1:0];
endmodule

