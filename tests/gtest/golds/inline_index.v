module Main (
    input [7:0] I0,
    input [7:0] I1,
    output O
);
wire [7:0] magma_Bits_8_add_inst0_out;
assign magma_Bits_8_add_inst0_out = 8'(I0 + I1);
assign O = magma_Bits_8_add_inst0_out[0];
endmodule

