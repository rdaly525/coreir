//This file is just included in context.cpp

Namespace* CoreIRLoadHeader_mantle(Context* c) {
  
  Namespace* mantle = c->newNamespace("mantle");

  //Change the name of rst and clr
  auto regFun = [](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
    bool en = args.at("has_en")->get<bool>();
    bool clr = args.at("has_clr")->get<bool>();
    bool rst = args.at("has_rst")->get<bool>();
    assert(!(clr && rst));
    Type* ptype = c->Bit()->Arr(width);

    RecordParams r({
        {"in" , ptype->getFlipped()},
        {"clk", c->Named("coreir.clkIn")},
        {"out", ptype}
    });
    if (en) r.push_back({"en",c->BitIn()});
    if (clr) r.push_back({"clr",c->BitIn()});
    if (rst) r.push_back({"rst",c->Named("coreir.rstIn")});
    return c->Record(r);
  };

  auto regModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    //if (genargs.at("has_rst")->get<bool>() || genargs.at("has_clr")->get<bool>()) {
      int width = genargs.at("width")->get<int>();
      modparams["init"] = BitVectorType::make(c,width);
      defaultargs["init"] = Const::make(c,BitVector(width,0));
    //}
    return {modparams,defaultargs};
  };

  Params regGenParams({
    {"width",c->Int()},
    {"has_en",c->Bool()},
    {"has_clr",c->Bool()},
    {"has_rst",c->Bool()}
  });
  TypeGen* regTypeGen = mantle->newTypeGen("regType",regGenParams,regFun);

  auto reg = mantle->newGeneratorDecl("reg",regTypeGen,regGenParams);
  reg->setModParamsGen(regModParamFun);
  reg->addDefaultGenArgs({{"has_en",Const::make(c,false)},{"has_clr",Const::make(c,false)},{"has_rst",Const::make(c,false)}});
  
  reg->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    int width = genargs.at("width")->get<int>();
    bool en = genargs.at("has_en")->get<bool>();
    bool clr = genargs.at("has_clr")->get<bool>();
    bool rst = genargs.at("has_rst")->get<bool>();

    auto io = def->getInterface();
    Values wval({{"width",Const::make(c,width)}});

    Wireable* reg;
    if (rst) {
      reg = def->addInstance("reg0","coreir.regrst",wval,{{"init",def->getModule()->getArg("init")}});
      def->connect("reg0.rst","self.rst");
    }
    else {
      reg = def->addInstance("reg0","coreir.reg",wval,{{"init",def->getModule()->getArg("init")}});
    }
    def->connect("reg0.out","self.out");
    def->connect("reg0.clk","self.clk");
    Wireable* toIn = reg->sel("in");
    
    if (en) {
      auto mux = def->addInstance("enMux","coreir.mux",wval);
      def->connect(mux->sel("out"),toIn);
      def->connect(mux->sel("in0"),reg->sel("out"));
      def->connect(mux->sel("sel"),io->sel("en"));
      toIn = mux->sel("in1");
    }
    if (clr) {
      auto mux = def->addInstance("clrMux","coreir.mux",wval);
      auto zero = def->addInstance("c0","coreir.const",wval,{{"value",Const::make(c,width,0)}});
      def->connect(mux->sel("out"),toIn);
      def->connect(mux->sel("in1"),zero->sel("out"));
      def->connect(mux->sel("sel"),io->sel("clr"));
      toIn = mux->sel("in0");
    }
    def->connect(io->sel("in"),toIn);
  });
  
  //Add

  auto addFun = [](Context* c, Values args) {
    int width = args.at("width")->get<int>();
    bool cin = args.at("has_cin")->get<bool>();
    bool cout = args.at("has_cout")->get<bool>();
    RecordParams r({
        {"in0" , c->BitIn()->Arr(width)},
        {"in1" , c->BitIn()->Arr(width)},
        {"out", c->Bit()->Arr(width)},
    });
    if (cin) r.push_back({"cin",c->BitIn()});
    if (cout) r.push_back({"cout",c->Bit()});
    return c->Record(r);
  };
  
  Params addGenParams({
    {"width",c->Int()},
    {"has_cin",c->Bool()},
    {"has_cout",c->Bool()},
  });
  TypeGen* addTypeGen = mantle->newTypeGen("addType",addGenParams,addFun);

  auto add = mantle->newGeneratorDecl("add",addTypeGen,addGenParams);
  add->addDefaultGenArgs({{"has_cin",Const::make(c,false)},{"has_cout",Const::make(c,false)}});
  auto sub = mantle->newGeneratorDecl("sub",addTypeGen,addGenParams);
  sub->addDefaultGenArgs({{"has_cin",Const::make(c,false)},{"has_cout",Const::make(c,false)}});

  return mantle;
}
