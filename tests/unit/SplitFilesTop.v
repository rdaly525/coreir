module SplitFilesTop (
    input I0,
    input I1,
    output O
);
wire and_inst0_out;
wire not_inst0_out;
corebit_and and_inst0 (
    .in0(not_inst0_out),
    .in1(I1),
    .out(and_inst0_out)
);
corebit_not not_inst0 (
    .in(I0),
    .out(not_inst0_out)
);
assign O = and_inst0_out;
endmodule

