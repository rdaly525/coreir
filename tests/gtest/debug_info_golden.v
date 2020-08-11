// Module `Term2` defined externally
// Module `And2` defined externally
module main (
    input [1:0] I,
    output O,
    output [1:0] O1
);
// Module `main` defined at tests/test_circuit/test_define.py:57
wire and2_0_O;
wire and2_1_O;
wire and2_2_O;
wire and2_3_O;
// Instance `and2_0` created at tests/test_circuit/test_define.py:61
// Connection `(and2_0.I0, I[0])` created at tests/test_circuit/test_define.py:63
// Connection `(and2_0.I1, I[1])` created at tests/test_circuit/test_define.py:64
And2 and2_0 (
    .I0(I[0]),
    .I1(I[1]),
    .O(and2_0_O)
);
// Instance `and2_1` created at tests/test_circuit/test_define.py:61
// Connection `(and2_1.I0, and2_0_O)` created at tests/test_circuit/test_define.py:66
// Connection `(and2_1.I1, I[1])` created at tests/test_circuit/test_define.py:67
And2 and2_1 (
    .I0(and2_0_O),
    .I1(I[1]),
    .O(and2_1_O)
);
// Instance `and2_2` created at tests/test_circuit/test_define.py:61
// Connection `(and2_2.I0, and2_1_O)` created at tests/test_circuit/test_define.py:66
// Connection `(and2_2.I1, I[1])` created at tests/test_circuit/test_define.py:67
And2 and2_2 (
    .I0(and2_1_O),
    .I1(I[1]),
    .O(and2_2_O)
);
// Instance `and2_3` created at tests/test_circuit/test_define.py:61
// Connection `(and2_3.I0, and2_2_O)` created at tests/test_circuit/test_define.py:66
// Connection `(and2_3.I1, I[1])` created at tests/test_circuit/test_define.py:67
And2 and2_3 (
    .I0(and2_2_O),
    .I1(I[1]),
    .O(and2_3_O)
);
// Instance `term0` created at tests/test_circuit/test_define.py:77
// Connection `(term0.I[1], and2_2_O)` created at tests/test_circuit/test_define.py:103
// Connection `(term0.I[0], and2_3_O)` created at tests/test_circuit/test_define.py:99
wire [1:0] term0_I;
assign term0_I = {and2_2_O,and2_3_O};
Term2 term0 (
    .I(term0_I)
);
// Connection `(O, and2_3_O)` created at tests/test_circuit/test_define.py:70
assign O = and2_3_O;
// Connection `(O1[0], and2_2_O)` created at tests/test_circuit/test_define.py:77
// Connection `(O1[1], and2_3_O)` created at tests/test_circuit/test_define.py:78
assign O1 = {and2_3_O,and2_2_O};
endmodule

