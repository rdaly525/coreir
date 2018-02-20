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
  
  Type* triPutType = c->Record({
    {"in",c->BitIn()},
    {"en",c->BitIn()},
    {"out",c->BitInOut()}
  });
  bitop->newModuleDecl("triput",triPutType);
  Type* triGetType = c->Record({
    {"in",c->BitInOut()},
    {"out",c->Bit()}
  });
  bitop->newModuleDecl("triget",triGetType);


  //TODO Add Halfadder/fulladder

  //Const and Term
  bitop->newModuleDecl("const",c->Record({{"out",c->Bit()}}),{{"value",c->Bool()}});
  bitop->newModuleDecl("term",c->Record({{"in",c->BitIn()}}));




  //State
  
  //DFF
  Type* dffType = c->Record({
    {"clk",c->Named("coreir.clkIn")},
    {"in",c->BitIn()},
    {"out",c->Bit()}
  });
  auto dff = bitop->newModuleDecl("dff",dffType,{{"init",c->Bool()}});
  dff->addDefaultModArgs({{"init",Const::make(c,false)}});

  //TODO Add other types of FFs (ones with reset and preset)

  Type* concatType = c->Record({
    {"in0", c->BitIn()},
    {"in1", c->BitIn()},
    {"out", c->Bit()->Arr(2)}
  });
  bitop->newModuleDecl("concat",concatType);

  return bitop;
}
