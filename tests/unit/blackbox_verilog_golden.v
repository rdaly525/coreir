// This is an important comment for foo!!
module foo (input I, output O);
    assign O = I;
endmodule
module top (
  input  I,
  output  O
);


  wire  inst0__I;
  wire  inst0__O;
  foo inst0(
    .I(inst0__I),
    .O(inst0__O)
  );

  assign inst0__I = I;

  assign O = inst0__O;


endmodule  // top

