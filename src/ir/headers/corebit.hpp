//This file is just included in context.cpp


//This should be loaded *AFTER* core
Namespace* CoreIRLoadHeader_corebit(Context* c) {

  Namespace* bitop = c->newNamespace("corebit");

  //Do The
  Type* bitBinaryType = c->Record({
    {"in0",c->BitIn()},
    {"in1",c->BitIn()},
    {"out",c->Bit()}
  });
  Type* bitTernaryType = c->Record({
    {"in0",c->BitIn()},
    {"in1",c->BitIn()},
    {"sel",c->BitIn()},
    {"out",c->Bit()}
  });
  Type* bitUnaryType = c->Record({
    {"in",c->BitIn()},
    {"out",c->Bit()}
  });

  vector<string> bitops = {"and","or","xor"};
  for (auto op : bitops) {
    bitop->newModuleDecl(op, bitBinaryType);
  }
  bitop->newModuleDecl("not",bitUnaryType);
  bitop->newModuleDecl("mux",bitTernaryType);
  bitop->newModuleDecl("wire",bitUnaryType);
  
  Type* triBufType = c->Record({
    {"in",c->BitIn()},
    {"en",c->BitIn()},
    {"out",c->BitInOut()}
  });
  bitop->newModuleDecl("tribuf",triBufType);
  Type* iBufType = c->Record({
    {"in",c->BitInOut()},
    {"out",c->Bit()}
  });
  bitop->newModuleDecl("ibuf",iBufType);
  bitop->newModuleDecl("pullresistor",c->Record({{"out",c->BitInOut()}}),{{"value",c->Bool()}});

  //TODO Add Halfadder/fulladder

  //Const and Term
  bitop->newModuleDecl("const",c->Record({{"out",c->Bit()}}),{{"value",c->Bool()}});
  bitop->newModuleDecl("term",c->Record({{"in",c->BitIn()}}));




  //State
  
  //reg
  Type* regType = c->Record({
    {"clk",c->Named("coreir.clkIn")},
    {"in",c->BitIn()},
    {"out",c->Bit()}
  });
  auto reg = bitop->newModuleDecl("reg",regType,{{"init",c->Bool()},{"clk_posedge",c->Bool()}});
  reg->addDefaultModArgs({{"init",Const::make(c,false)},{"clk_posedge",Const::make(c,true)}});

  //reg
  Type* regRstType = c->Record({
    {"clk",c->Named("coreir.clkIn")},
    {"arst",c->Named("coreir.arstIn")},
    {"in",c->BitIn()},
    {"out",c->Bit()}
  });
  auto regrst = bitop->newModuleDecl("reg_arst",regRstType,{{"init",c->Bool()},{"arst_posedge",c->Bool()},{"clk_posedge",c->Bool()}});
  regrst->addDefaultModArgs({{"init",Const::make(c,false)},{"arst_posedge",Const::make(c,true)},{"clk_posedge",Const::make(c,true)}});

  Type* concatType = c->Record({
    {"in0", c->BitIn()},
    {"in1", c->BitIn()},
    {"out", c->Bit()->Arr(2)}
  });
  bitop->newModuleDecl("concat",concatType);

  return bitop;
}
