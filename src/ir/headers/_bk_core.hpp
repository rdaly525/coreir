//This file is just included in context.cpp

void coreirprims_convert(Context* c, Namespace* coreirprims) {


  /* Name: slice
   * GenParams:
   *    lo: UINT, The start index of the slice
   *    hi: UINT, The stop index of the slice non-inclusive
   *    arrtype: TYPE, the array type of the input.
   * Type: In(arrtype) -> Out(arrtype.elemtype)[hi-lo+1]
   * Fun: out = in[lo:hi]
   * Argchecks:
   *    arrtype.isKind(ARRAY)
   *    start < stop <= arrtype.len
   */
  Params sliceParams({
    {"width",c->Int()},
    {"lo",c->Int()},
    {"hi",c->Int()}
  });
  auto sliceTypeGen = coreirprims->newTypeGen(
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
  auto slice = coreirprims->newGeneratorDecl("slice",sliceTypeGen,sliceParams);
  json jverilog;
  jverilog["parameters"] = {"width","lo","hi"};
  jverilog["prefix"] = "coreir_";
  slice->getMetaData()["verilog"] = jverilog;

  /* Name: concat
   * GenParams:
   *    larrtype: TYPE, the left array
   *    rarrtype: TYPE, the right array
   * Type: In(larrtype) -> In(rarrtype) -> Out(larrtype.elemtype)[larrtype.len+rarrtype.len]
   * Fun: out = concat(in[0],in[1])
   * Argchecks:
   *    larrtype.isKind(ARRAY)
   *    rarrtype.isKind(ARRAY)
   *    larrtype.elemtype == rarrtype.elemtype
   */
  Params concatParams({
    {"width0",c->Int()},
    {"width1",c->Int()}
  });
  auto concatTypeGen = coreirprims->newTypeGen(
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
  
  auto concat = coreirprims->newGeneratorDecl("concat",concatTypeGen,concatParams);
  jverilog["parameters"] = {"width0","width1"};
  jverilog["prefix"] = "coreir_";
  concat->getMetaData()["verilog"] = jverilog;

  /* Name: strip
   * GenParams:
   *    namedtype: TYPE, the type you want to strip
   * Type: namedtype -> namedtype.raw
   * Fun: out = in
   * Argchecks:
   *    namedtype.isKind(NAMED)
   */
  //Params stripParams({
  //  {"namedtype",TYPE}
  //});
  //auto stripFun = [](Context* c, Values args) { return c; } //TODO
  //TypeGen stripTypeGen(stripParams,stripFun);
  //stdlib->newGeneratorDecl("strip",stripParams,stripTypeGen);

  /* Name: cast
   * GenParams:
   *    intype: TYPE, precast type
   *    outtype: TYPE, postcast type
   * Type: intype -> outype
   * Fun: out = (outtype) in
   * Argchecks:
   *    intype.structure == outtype.structure
   */
  //Params castParams({
  //  {"intype",TYPE},
  //  {"outtype",TYPE}
  //});
  //auto castFun = [](Context* c, Values args) { return ; } //TODO
  //TypeGen castTypeGen(castParams,castFun);
  //stdlib->newGeneratorDecl("cast",castParams,castTypeGen);

}

void coreirprims_state(Context* c, Namespace* coreirprims) {

  //Template
  /* Name:
   * GenParams:
   *    <Argname>: <Argtype>, <description>
   * Type:
   * Fun:
   * Argchecks:
   */

  /* Name: reg
   * GenParams:
   *    regType: TYPE, Type of register
   *    en: BOOL, has enable?
   *    clr: BOOL, has clr port
   *    rst: BOOL, has asynchronous reset
   * ModParams
   *    resetval: UINT, value at reset
   * Type: {'in':regType
   * Fun: out <= (rst|clr) ? resetval : en ? in : out;
   * Argchecks:
   */
  auto regFun = [](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
    bool en = args.at("en")->get<bool>();
    bool clr = args.at("clr")->get<bool>();
    bool rst = args.at("rst")->get<bool>();
    assert(!(clr && rst));
    Type* ptype = c->Bit()->Arr(width);

    RecordParams r({
        {"in" , ptype->getFlipped()},
        {"clk", c->Named("coreir.clkIn")},
        {"out", ptype}
    });
    if (en) r.push_back({"en",c->BitIn()});
    if (clr) r.push_back({"clr",c->BitIn()});
    if (rst) r.push_back({"rst",c->BitIn()});
    return c->Record(r);
  };

  auto regModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    if (genargs.at("rst")->get<bool>() || genargs.at("clr")->get<bool>()) {
      int width = genargs.at("width")->get<int>();
      modparams["init"] = BitVectorType::make(c,width);
      defaultargs["init"] = Const::make(c,BitVector(width,0));
    }
    return {modparams,defaultargs};
  };

  //Set nameGen function
  auto regNameGen = [](Values args) {
    string name = "reg_P"; //TODO Should we do negedge?
    bool rst = args["rst"]->get<bool>();
    bool clr = args["clr"]->get<bool>();
    bool en = args["en"]->get<bool>();
    if (rst) name += "R";
    if (clr) name += "C";
    if (en) name += "E";
    return name;
  };

  Params regGenParams({
    {"width",c->Int()},
    {"en",c->Bool()},
    {"clr",c->Bool()},
    {"rst",c->Bool()}
  });
  TypeGen* regTypeGen = coreirprims->newTypeGen("regType",regGenParams,regFun);

  auto reg = coreirprims->newGeneratorDecl("reg",regTypeGen,regGenParams);
  reg->setModParamsGen(regModParamFun);
  reg->addDefaultGenArgs({{"en",Const::make(c,false)},{"clr",Const::make(c,false)},{"rst",Const::make(c,false)}});

  json jverilog;
  jverilog["parameters"] = {"width","init"};
  jverilog["prefix"] = "coreir_";
  reg->getMetaData()["verilog"] = jverilog;

  reg->setNameGen(regNameGen);


  auto bitRegFun = [](Context* c, Values args) {
    bool en = args.at("en")->get<bool>();
    bool clr = args.at("clr")->get<bool>();
    bool rst = args.at("rst")->get<bool>();
    assert(!(clr && rst));
    Type* ptype = c->Bit();

    RecordParams r({
        {"in" , ptype->getFlipped()},
        {"clk", c->Named("coreir.clkIn")},
        {"out", ptype}
    });
    if (en) r.push_back({"en",c->BitIn()});
    if (clr) r.push_back({"clr",c->BitIn()});
    if (rst) r.push_back({"rst",c->BitIn()});
    return c->Record(r);
  };
  Params bitRegGenParams({
    {"en",c->Bool()},
    {"clr",c->Bool()},
    {"rst",c->Bool()}
  });
  TypeGen* bitRegTypeGen = coreirprims->newTypeGen("bitRegType",bitRegGenParams,bitRegFun);
  auto bitreg = coreirprims->newGeneratorDecl("bitreg",bitRegTypeGen,bitRegGenParams);
  bitreg->addDefaultGenArgs({{"en",Const::make(c,false)},{"clr",Const::make(c,false)},{"rst",Const::make(c,false)}});
  bitreg->setModParamsGen({{"init",c->Bool()}},{{"init",Const::make(c,false)}});

  jverilog["parameters"] = {"init"};
  jverilog["prefix"] = "coreir_";
  bitreg->getMetaData()["verilog"] = jverilog;

  //Memory
  Params memGenParams({{"width",c->Int()},{"depth",c->Int()},{"has_init",c->Bool()}});
  auto memFun = [](Context* c, Values genargs) {
    int width = genargs.at("width")->get<int>();
    int depth = genargs.at("depth")->get<int>();
    ASSERT(isPower2(depth),"depth needs to be a power of 2: " + to_string(depth));
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
  
  auto memModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    bool has_init = genargs.at("has_init")->get<bool>();
    if (has_init) {
      int width = genargs.at("width")->get<int>();
      int depth = genargs.at("depth")->get<int>();
      modparams["init"] = BitVectorType::make(c,width*depth);
    }
    return {modparams,defaultargs};
  };


  TypeGen* memTypeGen = coreirprims->newTypeGen("memType",memGenParams,memFun);
  auto mem = coreirprims->newGeneratorDecl("mem",memTypeGen,memGenParams); 
  mem->setModParamsGen(memModParamFun);
  mem->addDefaultGenArgs({{"has_init",Const::make(c,true)}});
  jverilog["parameters"] = {"width","init"};
  jverilog["prefix"] = "coreir_";
  mem->getMetaData()["verilog"] = jverilog;

}

Namespace* CoreIRLoadLibrary_coreirprims(Context* c) {

  Namespace* coreirprims = c->newNamespace("coreir");

  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparams = Params({{"width",c->Int()}});

  //Single bit types
  coreirprims->newNamedType("clk","clkIn",c->Bit());
  coreirprims->newNamedType("rst","rstIn",c->Bit());

  //Array types
  //coreirprims->newNominalTypeGen("int","intIn",widthparams,arrfun);
  //coreirprims->newNominalTypeGen("uint","uintIn",widthparams,arrfun);

  //Common Function types
  coreirprims->newTypeGen(
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
  coreirprims->newTypeGen(
    "binary",
    widthparams,
    [](Context* c, Values args) {
      cout << "{" << Values2Str(args) << endl;
      uint width = args.at("width")->get<int>();
      cout << "}" << endl;
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"out",ptype}
      });
    }
  );
  //TODO should I change the width=1 -> bit for the reduces too?
  coreirprims->newTypeGen(
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
  coreirprims->newTypeGen(
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
  //coreirprims->newTypeGen(
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
  coreirprims->newTypeGen(
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

  /////////////////////////////////
  // Stdlib bitwise primitives
  //   not,and,or,xor,andr,orr,xorr,shl,lshr,ashr,dshl,dlshr,dashr
  /////////////////////////////////
  //coreirprims_bitwise(c,coreirprims);

  /////////////////////////////////
  // Stdlib Arithmetic primitives
  //   add,sub,mul,div,lt,leq,gt,geq,eq,neq,neg
  /////////////////////////////////


  json jverilog;
  jverilog["parameters"] = {"width"};
  jverilog["prefix"] = "coreir_";
  //Lazy way:
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = coreirprims->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      Generator* g = coreirprims->newGeneratorDecl(op,tg,widthparams);
      g->getMetaData()["verilog"] = jverilog;
    }
  }
  Params binaryCarryParams = Params(
    {
      {"width",c->Int()},
      {"has_cout",c->Bool()},
      {"has_cin",c->Bool()}
    }
  );
  coreirprims->newTypeGen(
    "binaryCarry",
    binaryCarryParams,
    [](Context* c, Values args) {
      int width = args.at("width")->get<int>();
      bool has_cout = args.at("has_cout")->get<bool>();
      bool has_cin  = args.at("has_cin")->get<bool>();
      Type* ptype = c->Bit()->Arr(width);
      RecordParams recordParams({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"out",ptype},
      });
      if (has_cout) recordParams.push_back({"cout", c->Bit()});
      if (has_cin) recordParams.push_back({"cin", c->BitIn()});
      return c->Record(recordParams);
    }
  );
  TypeGen* binaryCarryTypeGen = coreirprims->getTypeGen("binaryCarry");
  for (auto op : {"add", "sub"}) {
      Generator* genDecl = coreirprims->newGeneratorDecl(
        op, binaryCarryTypeGen, binaryCarryParams
      );
      genDecl->addDefaultGenArgs(
        {{"has_cout", Const::make(c,false)},
         {"has_cin", Const::make(c,false)}}
      );
      json binaryCarryVerilog;
      binaryCarryVerilog["parameters"] = {"width"};
      binaryCarryVerilog["prefix"] = "coreir_";
      genDecl->getMetaData()["verilog"] = binaryCarryVerilog;
  }

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

  //1 bit gen
  json bverilog;
  bverilog["prefix"] = "coreir_";
  vector<string> bitops = {"and","or","xor"};
  for (auto op : bitops) {
    coreirprims->newModuleDecl("bit" + op, bitBinaryType)->getMetaData()["verilog"] = bverilog;
  }
  coreirprims->newModuleDecl("bitnot",bitUnaryType)->getMetaData()["verilog"] = bverilog;
  coreirprims->newModuleDecl("bitmux",bitTernaryType)->getMetaData()["verilog"] = bverilog;


  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  //TODO
  //coreirprims_convert(c,coreirprims);

  //This defines a passthrough module. It is basically a nop that just passes the signal through
  Params passthroughParams({
    {"type",CoreIRType::make(c)},
  });
  TypeGen* passthroughTG = coreirprims->newTypeGen(
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
  coreirprims->newGeneratorDecl("passthrough",passthroughTG,passthroughParams);


  /////////////////////////////////
  // Stdlib stateful primitives
  //   reg, ram, rom
  /////////////////////////////////
  coreirprims_state(c,coreirprims);

  //Add Const
  coreirprims->newTypeGen(
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

  auto Const = coreirprims->newGeneratorDecl("const",coreirprims->getTypeGen("out"),widthparams);
  Const->setModParamsGen(constModParamFun);

  jverilog["parameters"] = {"width","value"};
  jverilog["prefix"] = "coreir_";
  Const->getMetaData()["verilog"] = jverilog;

  //Add bit version
  auto bitconst = coreirprims->newModuleDecl("bitconst",c->Record({{"out",c->Bit()}}),{{"value",c->Int()}});
  jverilog["parameters"] = {"value"};
  jverilog["prefix"] = "coreir_";
  bitconst->getMetaData()["verilog"] = jverilog;

  //Add Term
  coreirprims->newTypeGen(
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
  coreirprims->newGeneratorDecl("term",coreirprims->getTypeGen("in"),widthparams);

  coreirprims->newModuleDecl("bitterm",c->Record({{"in",c->BitIn()}}));

  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  coreirprims_convert(c,coreirprims);

  return coreirprims;
}
