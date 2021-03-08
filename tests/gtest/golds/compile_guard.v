module foo_corebit_term (
    input in
);

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
`ifdef ASSERT_ON
foo_ASSERT_ON_compile_guard ASSERT_ON_compile_guard (
    .I(I)
);
`endif
`ifndef ASSERT_ON
foo_ASSERT_ON_compile_guard ASSERT_ON_compile_guard_undefined (
    .I(I)
);
`endif
assign O = I;
endmodule

