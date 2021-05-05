module Top (
    input I,
    input I1,
    input I2,
    input I3,
    output O,
    output O1
);
assign O = (I ^ I) | ((~ I) & 1'b1);
assign O1 = I3 ? I2 : I1;
endmodule

