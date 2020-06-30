module coreir_undriven #(
    parameter width = 1
) (
    output [width-1:0] out
);

endmodule

module corebit_undriven (
    output out
);

endmodule

module Top (
    output O0,
    output [7:0] O1
);
corebit_undriven inst0 (
    .out(O0)
);
coreir_undriven #(
    .width(8)
) inst1 (
    .out(O1)
);
endmodule

