// Module `Buzz` defined externally
module Baz (
    input I,
    output O
);
Buzz O (
    .I(I),
    .O(O)
);
endmodule

module Bar (
    input I,
    output O
);
Baz O (
    .I(I),
    .O(O)
);
endmodule

module Foo (
    input I,
    output O0,
    output O1
);
Bar Bar_inst0 (
    .I(I),
    .O(O0)
);
Bar Bar_inst1 (
    .I(Bar_inst0.O.O.O),
    .O(O1)
);
endmodule

