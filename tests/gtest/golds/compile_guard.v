module foo_corebit_term (
    input in
);

endmodule

module foo_ASSERT_ON_compile_guard_with_output (
    input I,
    output O
);
assign O = I;
endmodule

module foo_ASSERT_ON_compile_guard (
    input I
);
foo_corebit_term corebit_term_inst0 (
    .in(I)
);
endmodule

module foo__Top (
    input I,
    output O
);
wire ASSERT_ON_compile_guard_O;
`ifdef ASSERT_ON
foo_ASSERT_ON_compile_guard_with_output ASSERT_ON_compile_guard (
    .I(I),
    .O(ASSERT_ON_compile_guard_O)
);
`else
assign ASSERT_ON_compile_guard_O = 0;
`endif
`ifndef ASSERT_ON
foo_ASSERT_ON_compile_guard ASSERT_ON_compile_guard_undefined (
    .I(I)
);
`endif
assign O = ASSERT_ON_compile_guard_O;
endmodule

