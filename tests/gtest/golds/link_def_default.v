// Module `STDCELLREG` defined externally
module my_register_synthesis (
    input [15:0] I,
    output [15:0] O,
    input CLK
);
STDCELLREG stdcell_reg (
    .I(I),
    .O(O),
    .CLK(CLK)
);
endmodule

module my_register (
    input [15:0] I,
    output [15:0] O,
    input CLK
);
STDCELLREG stdcell_reg (
    .I(I),
    .O(O),
    .CLK(CLK)
);

endmodule

