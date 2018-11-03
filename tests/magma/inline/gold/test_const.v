module test_const (
  input [7:0] I0,
  input [7:0] I1,
  output [7:0] O
);


  assign O[7:0] = I0 + I1 *'h03;


endmodule  // test_const

