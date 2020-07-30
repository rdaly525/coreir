module Main (
    input [7:0] I0 [16][12],
    input I1__0,
    input [2:0] I1__1,
    output [7:0] O0 [16][4],
    output [7:0] O1 [16][8],
    output [2:0] O2__0,
    output O2__1
);
assign O0 = {I0[3],I0[2],I0[1],I0[0]};
assign O1 = {I0[11],I0[10],I0[9],I0[8],I0[7],I0[6],I0[5],I0[4]};
assign O2__0 = I1__1;
assign O2__1 = I1__0;
endmodule

