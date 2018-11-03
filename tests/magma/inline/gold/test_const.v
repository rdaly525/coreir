module test_const (
  input [7:0] I0,
  input [7:0] I1,
  output [7:0] O
);


  // Inlined from const_3_8(width:8)(value:8'h03) : coreir.const
  wire [7:0] const_3_8__out;
  assign const_3_8__out = 8'h03;

  // Inlined from inst0(width:8)() : coreir.mul
  wire [7:0] inst0__in0;
  wire [7:0] inst0__in1;
  wire [7:0] inst0__out;
  assign inst0__out = inst0__in0 * inst0__in1;

  // Inlined from inst1(width:8)() : coreir.add
  wire [7:0] inst1__in0;
  wire [7:0] inst1__in1;
  wire [7:0] inst1__out;
  assign inst1__out = inst1__in0 + inst1__in1;

  assign inst0__in1[7:0] = const_3_8__out[7:0];

  assign inst0__in0[7:0] = I1[7:0];

  assign inst1__in1[7:0] = inst0__out[7:0];

  assign inst1__in0[7:0] = I0[7:0];

  assign O[7:0] = inst1__out[7:0];


endmodule  // test_const

