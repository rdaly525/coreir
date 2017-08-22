//Module: coreir_const defined externally
//Module: SB_LUT4 defined externally
//Module: SB_CARRY defined externally


module FullAdder(
  input  CIN,
  output  COUT,
  input  I0,
  input  I1,
  output  O
);

  //Wire declarations for instance 'inst1' (Module SB_CARRY)
  wire  inst1_I0;
  wire  inst1_CI;
  wire  inst1_I1;
  wire  inst1_CO;
  SB_CARRY inst1(
    .CI(inst1_CI),
    .I0(inst1_I0),
    .CO(inst1_CO),
    .I1(inst1_I1)
  );

  //Wire declarations for instance 'inst0' (Module SB_LUT4)
  wire  inst0_I0;
  wire  inst0_I1;
  wire  inst0_I2;
  wire  inst0_I3;
  wire  inst0_O;
  SB_LUT4 #(.LUT_INIT(38550)) inst0(
    .I0(inst0_I0),
    .I2(inst0_I2),
    .I1(inst0_I1),
    .O(inst0_O),
    .I3(inst0_I3)
  );

  //Wire declarations for instance 'const_inst0' (Module const)
  wire  const_inst0_out;
  coreir_const #(.width(1),.value(0)) const_inst0(
    .out(const_inst0_out)
  );

  //All the connections
  assign inst0_I3 = const_inst0_out;
  assign inst1_I1 = I1;
  assign inst0_I1 = I1;
  assign inst0_I0 = I0;
  assign inst1_I0 = I0;
  assign inst1_CI = CIN;
  assign inst0_I2 = CIN;
  assign O = inst0_O;
  assign COUT = inst1_CO;

endmodule //FullAdder
