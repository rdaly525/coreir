module Add8_cin (
  input  CIN,
  input [7:0] I0,
  input [7:0] I1,
  output [7:0] O
);


  assign O[7:0] = {1'0, 1'0, 1'0, 1'0, 1'0, 1'0, 1'0, CIN} + I0 + I1;


endmodule  // Add8_cin

module Sub8 (
  input [7:0] I0,
  input [7:0] I1,
  output [7:0] O
);


  wire  inst1__CIN;
  wire [7:0] inst1__I0;
  wire [7:0] inst1__I1;
  wire [7:0] inst1__O;
  Add8_cin inst1(
    .CIN(inst1__CIN),
    .I0(inst1__I0),
    .I1(inst1__I1),
    .O(inst1__O)
  );

  assign inst1__CIN = 1'1;

  assign inst1__I1[7:0] = ~I1;

  assign inst1__I0[7:0] = I0[7:0];

  assign O[7:0] = inst1__O[7:0];


endmodule  // Sub8

module test_two_ops (
  input [7:0] I0,
  input [7:0] I1,
  output [7:0] O
);


  wire [7:0] inst1__I0;
  wire [7:0] inst1__I1;
  wire [7:0] inst1__O;
  Sub8 inst1(
    .I0(inst1__I0),
    .I1(inst1__I1),
    .O(inst1__O)
  );

  assign inst1__I0[7:0] = I0 + I1;

  assign inst1__I1[7:0] = I0[7:0];

  assign O[7:0] = inst1__O[7:0];


endmodule  // test_two_ops

