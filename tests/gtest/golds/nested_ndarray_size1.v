module corebit_term (
    input in
);

endmodule

module Test (
    output [0:0] a [0:0],
    input [1:0] b [0:0]
);
corebit_term corebit_term_inst0 (
    .in(b[0][1])
);
assign a[0] = b[0][0];
endmodule

