module corebit_term (
    input in
);

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
`ifdef ASSERT_ON
ASSERT_ON_compile_guard ASSERT_ON_compile_guard (
    .I(I)
);
`endif
`ifndef ASSERT_ON
ASSERT_ON_compile_guard ASSERT_ON_compile_guard_invert (
    .I(I)
);
`endif
assign O = I;
endmodule

