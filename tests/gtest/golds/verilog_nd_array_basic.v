module Main (
    input [7:0] I0 [11:0][15:0],
    input I1__0,
    input [2:0] I1__1,
    output [7:0] O0 [3:0][15:0],
    output [7:0] O1 [7:0][15:0],
    output [2:0] O2__0,
    output O2__1
);
assign O0[3] = I0[3];
assign O0[2] = I0[2];
assign O0[1] = I0[1];
assign O0[0] = I0[0];
assign O1[7] = I0[11];
assign O1[6] = I0[10];
assign O1[5] = I0[9];
assign O1[4] = I0[8];
assign O1[3] = I0[7];
assign O1[2] = I0[6];
assign O1[1] = I0[5];
assign O1[0] = I0[4];
assign O2__0 = I1__1;
assign O2__1 = I1__0;
endmodule

