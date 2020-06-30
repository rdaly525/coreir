module Top_comb (
    output O_A/*verilator public*/
);
assign O_A = 1'b0;
endmodule

module Top (
    input CLK/*verilator public*/,
    output O_A/*verilator public*/
);
Top_comb Top_comb_inst0 (
    .O_A(O_A)
);
endmodule

