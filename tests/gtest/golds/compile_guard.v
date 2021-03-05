module corebit_term (
    input in
);

endmodule

module ASSERT_ON_compile_guard_with_output (
    input I,
    output O
);
assign O = I;
endmodule

module ASSERT_ON_compile_guard (
    input I
);
corebit_term corebit_term_inst0 (
    .in(I)
);
endmodule

module _Top (
    input I,
    output O
);
wire ASSERT_ON_compile_guard_O;
`ifdef ASSERT_ON
ASSERT_ON_compile_guard_with_output ASSERT_ON_compile_guard (
    .I(I),
    .O(ASSERT_ON_compile_guard_O)
);
`else
assign ASSERT_ON_compile_guard_O = 0;
`endif
`ifndef ASSERT_ON
ASSERT_ON_compile_guard ASSERT_ON_compile_guard_undefined (
    .I(I)
);
`endif
assign O = ASSERT_ON_compile_guard_O;
endmodule

