// Module `Add5` defined externally
module top (
    
);
wire [4:0] inst_out;
Add5 inst (
    .in(inst_out),
    .out(inst_out)
);
endmodule

