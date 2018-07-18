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
      ASSERT(lo < hi && hi<=width,"Bad slice args! lo="+to_string(lo) + ", hi=" + to_string(hi));
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

  Params extParams({
    {"width_in",c->Int()},
    {"width_out",c->Int()}
  });
  auto extTypeGen = core->newTypeGen(
    "extTypeFun",
    extParams,
    [](Context* c, Values args) {
      uint width_in = args.at("width_in")->get<int>();
      uint width_out = args.at("width_out")->get<int>();
      ASSERT(width_out >= width_in,"Bad valudes for widths");
      return c->Record({
        {"in",c->BitIn()->Arr(width_in)},
        {"out",c->Bit()->Arr(width_out)}
      });
    }
  );
  
  core->newGeneratorDecl("zext",extTypeGen,extParams);
  core->newGeneratorDecl("sext",extTypeGen,extParams);


  //strip
  Params stripParams({
    {"type",CoreIRType::make(c)}
  });
  auto stripTypeGen = core->newTypeGen(
    "stripTypeFun",
    stripParams,
    [](Context* c, Values args) {
      Type* type = args.at("type")->get<Type*>();
      ASSERT(isa<NamedType>(type),"type needs to be a named type");
      NamedType* ntype = cast<NamedType>(type);
      ASSERT(!ntype->isGen(),"NYI named type generators");
      ASSERT(ntype->getRaw()->isBaseType(), "NYI named type that is not Bit or BitIn");
      ASSERT(ntype->isOutput(), "NYI named types that are not outputs");
      return c->Record({
        {"in",ntype->getFlipped()},
        {"out",ntype->getRaw()}
      });
    }
  );
  core->newGeneratorDecl("strip",stripTypeGen,stripParams);

  //wrap
  Params wrapParams({
    {"type",CoreIRType::make(c)}
  });
  auto wrapTypeGen = core->newTypeGen(
    "wrapTypeFun",
    wrapParams,
    [](Context* c, Values args) {
      Type* type = args.at("type")->get<Type*>();
      ASSERT(isa<NamedType>(type),"type needs to be a named type");
      NamedType* ntype = cast<NamedType>(type);
      ASSERT(!ntype->isGen(),"NYI named type generators");
      ASSERT(ntype->getRaw()->isBaseType(), "NYI named type that is not Bit or BitIn");
      ASSERT(ntype->isOutput(), "NYI named type that is not output");
      return c->Record({
        {"in",ntype->getRaw()->getFlipped()},
        {"out",ntype}
      });
    }
  );
  core->newGeneratorDecl("wrap",wrapTypeGen,wrapParams);

}

void core_state(Context* c, Namespace* core) {

  Params widthparams = Params({{"width",c->Int()}});
  auto regModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    int width = genargs.at("width")->get<int>();
    modparams["init"] = BitVectorType::make(c,width);
    modparams["clk_posedge"] = c->Bool();
    string startString = "";
    for (int i = 0; i < width; i++) {
      startString += "x";
    }
    defaultargs["init"] = Const::make(c,BitVector(width, startString));
    defaultargs["clk_posedge"] = Const::make(c,true);
    return {modparams,defaultargs};
  };

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
  auto reg = core->newGeneratorDecl("reg",regTypeGen,widthparams);
  reg->setModParamsGen(regModParamFun);
  

  auto regRstModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    int width = genargs.at("width")->get<int>();
    modparams["init"] = BitVectorType::make(c,width);
    modparams["arst_posedge"] = c->Bool();
    modparams["clk_posedge"] = c->Bool();
    defaultargs["arst_posedge"] = Const::make(c,true);
    defaultargs["clk_posedge"] = Const::make(c,true);
    return {modparams,defaultargs};
  };

  auto regRstFun = [](Context* c, Values args) {
    int width = args.at("width")->get<int>();
    return c->Record({
        {"clk", c->Named("coreir.clkIn")},
        {"arst", c->Named("coreir.arstIn")},
        {"in" , c->BitIn()->Arr(width)},
        {"out", c->Bit()->Arr(width)}
    });
  };


  TypeGen* regRstTypeGen = core->newTypeGen("regRstType",widthparams,regRstFun);
  auto regRst = core->newGeneratorDecl("reg_arst",regRstTypeGen,widthparams);
  regRst->setModParamsGen(regRstModParamFun);

  //Memory
  Params memGenParams({{"width",c->Int()},{"depth",c->Int()},{"has_init",c->Bool()}});
  auto memFun = [](Context* c, Values genargs) {
    int width = genargs.at("width")->get<int>();
    int depth = genargs.at("depth")->get<int>();
    int awidth = ceil(std::log2(depth));
    return c->Record({
      {"clk",c->Named("coreir.clkIn")},
      {"wdata",c->BitIn()->Arr(width)},
      {"waddr",c->BitIn()->Arr(awidth)},
      {"wen",c->BitIn()},
      {"rdata",c->Bit()->Arr(width)},
      {"raddr",c->BitIn()->Arr(awidth)}
    });
  };
  
  auto memModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    bool has_init = genargs.at("has_init")->get<bool>();
    if (has_init) {
      modparams["init"] = JsonType::make(c);
    }
    return {modparams,defaultargs};
  };

  TypeGen* memTypeGen = core->newTypeGen("memType",memGenParams,memFun);
  Generator* mem = core->newGeneratorDecl("mem",memTypeGen,memGenParams); 
  mem->setModParamsGen(memModParamFun);
  mem->addDefaultGenArgs({{"has_init",Const::make(c,false)}});

}

Namespace* CoreIRLoadHeader_core(Context* c) {

  Namespace* core = c->newNamespace("coreir");

  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparams = Params({{"width",c->Int()}});

  //Single bit types
  core->newNamedType("clk","clkIn",c->Bit());
  core->newNamedType("arst","arstIn",c->Bit());

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
  
  TypeGen* tribufTG = core->newTypeGen(
    "triBuf",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)},
        {"en",c->BitIn()},
        {"out",c->BitInOut()->Arr(width)}
      });
    }
  );
  core->newGeneratorDecl("tribuf",tribufTG,widthparams);
  
  TypeGen* ibufTG = core->newTypeGen(
    "iBuf",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      return c->Record({
        {"in",c->BitInOut()->Arr(width)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
  core->newGeneratorDecl("ibuf",ibufTG,widthparams);
  
  core->newTypeGen(
    "pullResistor",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();

      return c->Record({
        {"out",c->BitInOut()->Arr(width)}
      });
    }
  );
  
  auto pullresistorModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    int width = genargs.at("width")->get<int>();
    Params modparams;
    modparams["value"] = BitVectorType::make(c,width);
    return {modparams,Values()};
  };

  auto pr = core->newGeneratorDecl("pullresistor",core->getTypeGen("pullResistor"),widthparams);
  pr->setModParamsGen(pullresistorModParamFun);


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

  return core;
}
