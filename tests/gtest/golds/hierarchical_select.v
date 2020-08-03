// Module `Baz` defined externally
module Bar (
    input I,
    output O
);
wire Baz_inst0_I;
assign Baz_inst0_I = I;
Baz Baz_inst0 (
    .I(Baz_inst0_I),
    .O(O)
);
endmodule

module Foo (
    input I,
    output O0,
    output O1
);
wire Bar_inst0_I;
wire Bar_inst1_I;
assign Bar_inst0_I = I;
Bar Bar_inst0 (
    .I(Bar_inst0_I),
    .O(O0)
);
assign Bar_inst1_I = Bar_inst0.Baz_inst0.O;
Bar Bar_inst1 (
    .I(Bar_inst1_I),
    .O(O1)
);
endmodule

