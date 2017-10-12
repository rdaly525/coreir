//This file is just included in context.cpp

void core_convert(Context* c, Namespace* core) {

  Params sliceParams({
    {"width",c->Int()},
    {"lo",c->Int()},
    {"hi",c->Int()}
  });
  auto sliceTypeGen = core->newTypeGen(
    "sliceTypeFun",
    sliceParams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      uint lo = args.at("lo")->get<int>();
      uint hi = args.at("hi")->get<int>();
      ASSERT(lo < hi && hi<=width,"Bad slice args!");
      return c->Record({
        {"in",c->BitIn()->Arr(width)},
        {"out",c->Bit()->Arr(hi-lo)}
      });
    }
  );
  core->newGeneratorDecl("slice",sliceTypeGen,sliceParams);

  Params concatParams({
    {"width0",c->Int()},
    {"width1",c->Int()}
  });
  auto concatTypeGen = core->newTypeGen(
    "concatTypeFun",
    concatParams,
    [](Context* c, Values args) {
      uint width0 = args.at("width0")->get<int>();
      uint width1 = args.at("width1")->get<int>();
      return c->Record({
        {"in0",c->BitIn()->Arr(width0)},
        {"in1",c->BitIn()->Arr(width1)},
        {"out",c->Bit()->Arr(width0+width1)}
      });
    }
  );
  
  core->newGeneratorDecl("concat",concatTypeGen,concatParams);

  //TODO sign extend
  //TODO zero extend
  //TODO repeat

}

void core_state(Context* c, Namespace* core) {

  Params widthparams = Params({{"width",c->Int()}});

  //Reg does not have a reset/init
  auto regFun = [](Context* c, Values args) {
    int width = args.at("width")->get<int>();
    return c->Record({
        {"clk", c->Named("coreir.clkIn")},
        {"in" , c->BitIn()->Arr(width)},
        {"out", c->Bit()->Arr(width)}
    });
  };

  TypeGen* regTypeGen = core->newTypeGen("regType",widthparams,regFun);
  core->newGeneratorDecl("reg",regTypeGen,widthparams);
  


  auto regRstFun = [](Context* c, Values args) {
    int width = args.at("width")->get<int>();
    return c->Record({
        {"clk", c->Named("coreir.clkIn")},
        {"rst", c->Named("coreir.rstIn")},
        {"in" , c->BitIn()->Arr(width)},
        {"out", c->Bit()->Arr(width)}
    });
  };

  auto regRstModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    int width = genargs.at("width")->get<int>();
    modparams["init"] = BitVectorType::make(c,width);
    defaultargs["init"] = Const::make(c,BitVector(width,0));
    return {modparams,defaultargs};
  };

  TypeGen* regRstTypeGen = core->newTypeGen("regRstType",widthparams,regRstFun);
  auto regRst = core->newGeneratorDecl("regrst",regRstTypeGen,widthparams);
  regRst->setModParamsGen(regRstModParamFun);

  //TODO Deal with roms
  //Memory
  Params memGenParams({{"width",c->Int()},{"depth",c->Int()}});
  auto memFun = [](Context* c, Values genargs) {
    int width = genargs.at("width")->get<int>();
    int depth = genargs.at("depth")->get<int>();
    ASSERT(isPower2(depth),"depth needs to be a power of 2: " + to_string(depth)); // TODO fix this
    int awidth = uint(std::log2(depth));
    return c->Record({
      {"clk",c->Named("coreir.clkIn")},
      {"wdata",c->BitIn()->Arr(width)},
      {"waddr",c->BitIn()->Arr(awidth)},
      {"wen",c->BitIn()},
      {"rdata",c->Bit()->Arr(width)},
      {"raddr",c->BitIn()->Arr(awidth)}
    });
  };
  
  //auto memModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
  //  Params modparams;
  //  Values defaultargs;
  //  bool has_init = genargs.at("has_init")->get<bool>();
  //  if (has_init) {
  //    int width = genargs.at("width")->get<int>();
  //    int depth = genargs.at("depth")->get<int>();
  //    modparams["init"] = BitVectorType::make(c,width*depth);
  //  }
  //  return {modparams,defaultargs};
  //};

  TypeGen* memTypeGen = core->newTypeGen("memType",memGenParams,memFun);
  core->newGeneratorDecl("mem",memTypeGen,memGenParams); 
  //mem->setModParamsGen(memModParamFun);

}

Namespace* CoreIRLoadHeader_core(Context* c) {

  Namespace* core = c->newNamespace("coreir");

  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparams = Params({{"width",c->Int()}});

  //Single bit types
  core->newNamedType("clk","clkIn",c->Bit());
  core->newNamedType("rst","rstIn",c->Bit());

  //Common Function types
  core->newTypeGen(
    "unary",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in",c->Flip(ptype)},
        {"out",ptype}
      });
    }
  );
  core->newTypeGen(
    "binary",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"out",ptype}
      });
    }
  );
  
  core->newTypeGen(
    "binaryReduce",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"out",c->Bit()}
      });
    }
  );
  core->newTypeGen(
    "unaryReduce",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in",c->Flip(ptype)},
        {"out",c->Bit()}
      });
    }
  );

  ////For repeat
  //core->newTypeGen(
  //  "unaryExpand",
  //  widthparams,
  //  [](Context* c, Values args) {
  //    uint width = args.at("width")->get<int>();
  //    return c->Record({
  //      {"in",c->BitIn()},
  //      {"out",c->Bit()->Arr(width)}
  //    });
  //  }
  //);
  
  //For mux
  core->newTypeGen(
    "muxType",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"sel",c->BitIn()},
        {"out",ptype}
      });
    }
  );

  //Add all the generators (with widthparams)
  for (auto tmap : coreMap) {
    TypeGen* tg = core->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      core->newGeneratorDecl(op,tg,widthparams);
    }
  }

  /////////////////////////////////
  // Stdlib stateful primitives
  //   reg, ram, rom
  /////////////////////////////////
  core_state(c,core);

  //Add Const
  core->newTypeGen(
    "out",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);

      return c->Record({
        {"out",ptype}
      });
    }
  );

  auto constModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    int width = genargs.at("width")->get<int>();
    Params modparams;
    modparams["value"] = BitVectorType::make(c,width);
    return {modparams,Values()};
  };

  auto Const = core->newGeneratorDecl("const",core->getTypeGen("out"),widthparams);
  Const->setModParamsGen(constModParamFun);

  //Add Term
  core->newTypeGen(
    "in",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in",ptype->getFlipped()}
      });
    }
  );
  core->newGeneratorDecl("term",core->getTypeGen("in"),widthparams);

  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  core_convert(c,core);


  //TODO for now keep passthrough here.

  //This defines a passthrough module. It is basically a nop that just passes the signal through
  Params passthroughParams({
    {"type",CoreIRType::make(c)},
  });
  TypeGen* passthroughTG = core->newTypeGen(
    "passthrough",
    passthroughParams,
    [](Context* c, Values args) {
      Type* t = args.at("type")->get<Type*>();
      return c->Record({
        {"in",t->getFlipped()},
        {"out",t}
      });
    }
  );
  core->newGeneratorDecl("passthrough",passthroughTG,passthroughParams);


  return core;
}
