module foo_bar_Foo (
    input I,
    output O
);

always @(*) begin
    O = I;
    $display("%d\n", I);
end

endmodule

