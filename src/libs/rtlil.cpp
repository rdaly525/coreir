#include "coreir/libs/rtlil.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(rtlil);

using namespace std;
using namespace CoreIR;

bool signMatters(const std::string& opName) {
  vector<string> signInvOps{"and", "or", "xor", "add", "sub", "mul"};
  return !elem(opName, signInvOps);
}

std::string rtlilSignedComparatorName(const std::string& name) {
  if (name == "lt") {
    return "coreir.slt";
  }

  if (name == "gt") {
    return "coreir.sgt";
  }

  if (name == "ge") {
    return "coreir.sge";
  }

  if (name == "le") {
    return "coreir.sle";
  }

  if (name == "eq") {
    return "coreir.eq";
  }

  if (name == "ne") {
    return "coreir.neq";
  }

  cout << "Unsupported signed comparator " << name << endl;
  assert(false);
}

std::string rtlilCorebitName(const std::string& name) {
  if (name == "and") {
    return "corebit.and";
  }

  if (name == "or") {
    return "corebit.or";
  }

  if (name == "xor") {
    return "corebit.xor";
  }
  
  assert(false);
}

std::string rtlilCoreirName(const std::string& name) {
  
  if (name == "shl") {
    return "coreir.shl";
  }

  if (name == "shr") {
    return "coreir.lshr";
  }

  if (name == "sshr") {
    return "coreir.ashr";
  }
  
  if (name == "not") {
    return "coreir.not";
  }

  if (name == "reduce_or") {
    return "coreir.orr";
  }

  if (name == "reduce_bool") {
    return "coreir.orr";
  }
  
  if (name == "reduce_and") {
    return "coreir.andr";
  }

  if (name == "reduce_xor") {
    return "coreir.xorr";
  }
  
  if (name == "add") {
    return "coreir.add";
  }

  if (name == "sub") {
    return "coreir.sub";
  }

  if (name == "mul") {
    return "coreir.mul";
  }
  
  if (name == "and") {
    return "coreir.and";
  }

  if (name == "or") {
    return "coreir.or";
  }

  if (name == "xor") {
    return "coreir.xor";
  }

  if (name == "eq") {
    return "coreir.eq";
  }

  if (name == "ne") {
    return "coreir.neq";
  }

  // TODO: Distinguish signed / unsigned
  if (name == "ge") {
    return "coreir.uge";
  }

  if (name == "le") {
    return "coreir.ule";
  }

  if (name == "gt") {
    return "coreir.ugt";
  }

  if (name == "lt") {
    return "coreir.ult";
  }
  
  cout << "Unsupported name = " << name << endl;
  assert(false);
}

Namespace* CoreIRLoadLibrary_rtlil(CoreIR::Context* c) {
  auto rtLib = c->newNamespace("rtlil");

  // Operation related nodes
  vector<string> rtlilBinops{"and", "or", "xor", "xnor",
      "shl", "shr", "sshl", "sshr",
      "logic_and", "logic_or",
      "eqx", "nex", "lt", "le", "eq", "ne", "ge", "gt",
      "add", "sub", "mul", "div", "mod", "pow"};

  for (auto& name : rtlilBinops) {
    Params binopParams = {{"A_SIGNED", c->Bool()},
                          {"B_SIGNED", c->Bool()},
                          {"A_WIDTH", c->Int()},
                          {"B_WIDTH", c->Int()},
                          {"Y_WIDTH", c->Int()}};
    TypeGen* logic_andTP =
      rtLib->newTypeGen(
                        name,
                        binopParams,
                        [](Context* c, Values genargs) {
                          uint a_width = genargs.at("A_WIDTH")->get<int>();
                          uint b_width = genargs.at("B_WIDTH")->get<int>();
                          uint y_width = genargs.at("Y_WIDTH")->get<int>();

                          return c->Record({
                              {"A", c->BitIn()->Arr(a_width)},
                                {"B", c->BitIn()->Arr(b_width)},
                                  {"Y",c->Bit()->Arr(y_width)}});
                        });

    rtLib->newGeneratorDecl(name, logic_andTP, binopParams);
    
  }

  // Definitions for binops

  // - Shift operations, ignoring sshl
  vector<string> rtlilShifts{"shl", "shr", "sshr"};
  for (auto& name : rtlilShifts) {
    auto gen = rtLib->getGenerator(name);

    std::function<void (Context*, Values, ModuleDef*)> genFun =
      [name](Context* c, Values args, ModuleDef* def) {
      uint a_width = args.at("A_WIDTH")->get<int>();
      uint b_width = args.at("B_WIDTH")->get<int>();
      uint y_width = args.at("Y_WIDTH")->get<int>();

      // Does it matter whether a shift operand is signed or not? sshr vs shr
      // is what determines whether to zero extend or not right?
      // bool a_signed = args.at("A_SIGNED")->get<bool>();
      // bool b_signed = args.at("B_SIGNED")->get<bool>();

      // ASSERT(!a_signed, "Have not yet added signed input support for " + name);
      // ASSERT(!b_signed, "Have not yet added signed shift value support for " + name);

      ASSERT(y_width >= a_width, "Shift operations must have output at least as long as bit vector being shifted");

      uint res_width = max(a_width, y_width);
      uint ext_width = max(res_width, b_width);

      def->addInstance("extendA",
                       "coreir.zext",
      {{"width_in", Const::make(c, a_width)},
          {"width_out", Const::make(c, ext_width)}});

      def->addInstance("extendB",
                       "coreir.zext",
      {{"width_in", Const::make(c, b_width)},
          {"width_out", Const::make(c, ext_width)}});

      string opGenName = rtlilCoreirName(name);
      def->addInstance("op0", opGenName, {{"width", Const::make(c, ext_width)}});

      def->addInstance("slice0", "coreir.slice",
      {{"width", Const::make(c, ext_width)},
          {"lo", Const::make(c, 0)},
            {"hi", Const::make(c, res_width)}});

      def->connect("self.A", "extendA.in");
      def->connect("self.B", "extendB.in");
        
      def->connect("extendA.out", "op0.in0");
      def->connect("extendB.out", "op0.in1");

      def->connect("op0.out", "slice0.in");
      def->connect("slice0.out", "self.Y");
    };

    gen->setGeneratorDefFromFun(genFun);
    
  }

  // - Bitwise and arithmetic operations
  vector<string> rtlilBitwise{"and", "or", "xor", "add", "sub", "mul"};
  for (auto& name : rtlilBitwise) {
    auto gen = rtLib->getGenerator(name);

    std::function<void (Context*, Values, ModuleDef*)> genFun =
      [name](Context* c, Values args, ModuleDef* def) {
      uint a_width = args.at("A_WIDTH")->get<int>();
      uint b_width = args.at("B_WIDTH")->get<int>();
      uint y_width = args.at("Y_WIDTH")->get<int>();

      bool a_signed = args.at("A_SIGNED")->get<bool>();
      bool b_signed = args.at("B_SIGNED")->get<bool>();

      bool signsMatter = signMatters(name);

      if (a_signed || b_signed) {
        cout << "operation = " << name << endl;
        cout << "a_signed = " << a_signed << endl;
        cout << "b_signed = " << b_signed << endl;
      }
      
      ASSERT(!signsMatter || (!a_signed && !b_signed), "Have not yet added signed arithmetic support for RTLIL");

      // ASSERT(!a_signed, "Have not yet added signed arithmetic support for RTLIL");
      // ASSERT(!b_signed, "Have not yet added signed arithmetic support for RTLIL");

      ASSERT(y_width >= a_width, "Bitwise and arithmetic operations must have output at least as long as operands");
      ASSERT(y_width >= b_width, "Bitwise and arithmetic operations must have output at least as long as operands");

      uint ext_width = y_width;

      def->addInstance("extendA",
                       "coreir.zext",
      {{"width_in", Const::make(c, a_width)},
          {"width_out", Const::make(c, ext_width)}});

      def->addInstance("extendB",
                       "coreir.zext",
      {{"width_in", Const::make(c, b_width)},
          {"width_out", Const::make(c, ext_width)}});

      string opGenName = rtlilCoreirName(name);
      def->addInstance("op0", opGenName, {{"width", Const::make(c, ext_width)}});

      def->connect("self.A", "extendA.in");
      def->connect("self.B", "extendB.in");
        
      def->connect("extendA.out", "op0.in0");
      def->connect("extendB.out", "op0.in1");

      def->connect("op0.out", "self.Y");
    };

    gen->setGeneratorDefFromFun(genFun);
    
  }

  // - Comparators
  vector<string> rtlilBinaryComps{"eqx", "nex", "lt", "le", "eq", "ne", "ge", "gt"};
  for (auto& name : rtlilBinaryComps) {
    auto gen = rtLib->getGenerator(name);

    std::function<void (Context*, Values, ModuleDef*)> genFun =
      [name](Context* c, Values args, ModuleDef* def) {
        uint a_width = args.at("A_WIDTH")->get<int>();
        uint b_width = args.at("B_WIDTH")->get<int>();
        uint y_width = args.at("Y_WIDTH")->get<int>();

        ASSERT(y_width == 1, "Output of a comparator must be 1 bit!");

        bool a_signed = args.at("A_SIGNED")->get<bool>();
        bool b_signed = args.at("B_SIGNED")->get<bool>();

        bool bothSigned = false;
        if (a_signed && b_signed) {
          bothSigned = true;
        } else {
          if (a_signed || b_signed) {
            cout << "operation = " << name << endl;
            cout << "a_signed = " << a_signed << endl;
            cout << "b_signed = " << b_signed << endl;
          }

          ASSERT(!a_signed, "Have not yet added signed comparator support for RTLIL");
          ASSERT(!b_signed, "Have not yet added signed comparator support for RTLIL");
        }


        uint ext_width = max(a_width, b_width);

        def->addInstance("extendA",
                         "coreir.zext",
      {{"width_in", Const::make(c, a_width)},
          {"width_out", Const::make(c, ext_width)}});

        def->addInstance("extendB",
                         "coreir.zext",
      {{"width_in", Const::make(c, b_width)},
          {"width_out", Const::make(c, ext_width)}});

        string opGenName;
        if (bothSigned) {
          opGenName = rtlilSignedComparatorName(name);
        } else {
          opGenName = rtlilCoreirName(name);
        }
        def->addInstance("op0", opGenName, {{"width", Const::make(c, ext_width)}});

        def->connect("self.A", "extendA.in");
        def->connect("self.B", "extendB.in");

        def->connect("extendA.out", "op0.in0");
        def->connect("extendB.out", "op0.in1");

        def->connect("op0.out", "self.Y.0");
    };

    gen->setGeneratorDefFromFun(genFun);

  }

  auto logicOrGen = rtLib->getGenerator("logic_or");

  std::function<void (Context*, Values, ModuleDef*)> logicOrGenFun =
    [](Context* c, Values args, ModuleDef* def) {
    uint a_width = args.at("A_WIDTH")->get<int>();
    uint b_width = args.at("B_WIDTH")->get<int>();
    uint y_width = args.at("Y_WIDTH")->get<int>();

    ASSERT(y_width == 1, "Output of a comparator must be 1 bit!");

    bool a_signed = args.at("A_SIGNED")->get<bool>();
    bool b_signed = args.at("B_SIGNED")->get<bool>();

    ASSERT(!a_signed, "Have not yet added signed logic_or support for RTLIL");
    ASSERT(!b_signed, "Have not yet added signed logic_or support for RTLIL");

    uint ext_width = max(a_width, b_width);

    def->addInstance("extendA",
                     "coreir.zext",
    {{"width_in", Const::make(c, a_width)},
        {"width_out", Const::make(c, ext_width)}});

    def->addInstance("extendB",
                     "coreir.zext",
    {{"width_in", Const::make(c, b_width)},
        {"width_out", Const::make(c, ext_width)}});

    def->addInstance("aRed", "coreir.orr", {{"width", Const::make(c, ext_width)}});
    def->addInstance("bRed", "coreir.orr", {{"width", Const::make(c, ext_width)}});
    def->addInstance("orOps", "corebit.or");

    def->connect("self.A", "extendA.in");
    def->connect("self.B", "extendB.in");

    def->connect("extendA.out", "aRed.in");
    def->connect("extendB.out", "bRed.in");

    def->connect("orOps.in0", "aRed.out");
    def->connect("orOps.in1", "bRed.out");
    
    def->connect("orOps.out", "self.Y.0");
  };

  logicOrGen->setGeneratorDefFromFun(logicOrGenFun);
  
  auto logicAndGen = rtLib->getGenerator("logic_and");

  std::function<void (Context*, Values, ModuleDef*)> logicAndGenFun =
    [](Context* c, Values args, ModuleDef* def) {
    uint a_width = args.at("A_WIDTH")->get<int>();
    uint b_width = args.at("B_WIDTH")->get<int>();
    uint y_width = args.at("Y_WIDTH")->get<int>();

    ASSERT(y_width == 1, "Output of a comparator must be 1 bit!");

    bool a_signed = args.at("A_SIGNED")->get<bool>();
    bool b_signed = args.at("B_SIGNED")->get<bool>();

    ASSERT(!a_signed, "Have not yet added signed logic_and support for RTLIL");
    ASSERT(!b_signed, "Have not yet added signed logic_and support for RTLIL");

    uint ext_width = max(a_width, b_width);

    def->addInstance("extendA",
                     "coreir.zext",
    {{"width_in", Const::make(c, a_width)},
        {"width_out", Const::make(c, ext_width)}});

    def->addInstance("extendB",
                     "coreir.zext",
    {{"width_in", Const::make(c, b_width)},
        {"width_out", Const::make(c, ext_width)}});

    def->addInstance("aRed", "coreir.orr", {{"width", Const::make(c, ext_width)}});
    def->addInstance("bRed", "coreir.orr", {{"width", Const::make(c, ext_width)}});
    def->addInstance("andOps", "corebit.and");

    def->connect("self.A", "extendA.in");
    def->connect("self.B", "extendB.in");

    def->connect("extendA.out", "aRed.in");
    def->connect("extendB.out", "bRed.in");

    def->connect("andOps.in0", "aRed.out");
    def->connect("andOps.in1", "bRed.out");
    
    def->connect("andOps.out", "self.Y.0");
  };

  logicAndGen->setGeneratorDefFromFun(logicAndGenFun);
  
  // Unary operation declarations
  vector<string> rtlilUnops{"not", "pos", "neg", "reduce_and", "reduce_or", "reduce_xor", "reduce_xnor", "reduce_bool", "logic_not"};

  for (auto& name : rtlilUnops) {
    Params binopParams = {{"A_SIGNED", c->Bool()},
                          {"A_WIDTH", c->Int()},
                          {"Y_WIDTH", c->Int()}};
    TypeGen* logic_andTP =
      rtLib->newTypeGen(
                        name,
                        binopParams,
                        [](Context* c, Values genargs) {
                          uint a_width = genargs.at("A_WIDTH")->get<int>();
                          uint y_width = genargs.at("Y_WIDTH")->get<int>();

                          return c->Record({
                              {"A", c->BitIn()->Arr(a_width)},
                                {"Y",c->Bit()->Arr(y_width)}});
                        });

    rtLib->newGeneratorDecl(name, logic_andTP, binopParams);
    
  }

  // Unary operator implementations
  auto notGen = rtLib->getGenerator("not");

  std::function<void (Context*, Values, ModuleDef*)> genFun =
    [](Context* c, Values args, ModuleDef* def) {
    uint a_width = args.at("A_WIDTH")->get<int>();
    uint y_width = args.at("Y_WIDTH")->get<int>();
    uint ext_width = y_width;

    ASSERT(y_width >= a_width, "Output of not must be at least as large as its input");

    bool a_signed = args.at("A_SIGNED")->get<bool>();

    ASSERT(!a_signed, "Have not yet added signed negation support for RTLIL");

    def->addInstance("extendA",
                     "coreir.zext",
    {{"width_in", Const::make(c, a_width)},
        {"width_out", Const::make(c, ext_width)}});
    
    string opGenName = rtlilCoreirName("not");
    def->addInstance("op0", opGenName, {{"width", Const::make(c, y_width)}});

    def->connect("self.A", "extendA.in");
    def->connect("extendA.out", "op0.in");
    def->connect("op0.out", "self.Y");
  };

  notGen->setGeneratorDefFromFun(genFun);

  auto logicNotGen = rtLib->getGenerator("logic_not");

  std::function<void (Context*, Values, ModuleDef*)> lnotGenFun =
    [](Context* c, Values args, ModuleDef* def) {
    uint a_width = args.at("A_WIDTH")->get<int>();
    uint y_width = args.at("Y_WIDTH")->get<int>();

    ASSERT(y_width == 1, "Output of logic_not must be 1 bit");

    bool a_signed = args.at("A_SIGNED")->get<bool>();

    ASSERT(!a_signed, "Have not yet added signed negation support for rtlil.logic_not");

    def->addInstance("reduce", "coreir.orr", {{"width", Const::make(c, a_width)}});
    def->addInstance("negate", "corebit.not");

    def->connect("self.A", "reduce.in");
    def->connect("reduce.out", "negate.in");
    def->connect("negate.out", "self.Y.0");

    // string opGenName = rtlilCoreirName("not");
    // def->addInstance("op0", opGenName, {{"width", Const::make(c, y_width)}});

    // def->connect("self.A", "extendA.in");
    // def->connect("extendA.out", "op0.in");
    // def->connect("op0.out", "self.Y");
  };

  logicNotGen->setGeneratorDefFromFun(lnotGenFun);
  

  // Reduction ops
  vector<string> rtlilReduceOps{"reduce_and", "reduce_or", "reduce_xor", "reduce_bool"};
  for (auto& name : rtlilReduceOps) {
    auto gen = rtLib->getGenerator(name);

    std::function<void (Context*, Values, ModuleDef*)> genFun =
      [name](Context* c, Values args, ModuleDef* def) {
        uint a_width = args.at("A_WIDTH")->get<int>();
        uint y_width = args.at("Y_WIDTH")->get<int>();

        ASSERT(y_width == 1, "Output of a logical reduce must be 1 bit!");

        //bool a_signed = args.at("A_SIGNED")->get<bool>();

        // NOTE: For reducing booleans signed vs unsigned should not matter
        //ASSERT(!a_signed, "Have not yet added signed reduce support for RTLIL");

        string opGenName = rtlilCoreirName(name);
        def->addInstance("op0", opGenName, {{"width", Const::make(c, a_width)}});

        def->connect("self.A", "op0.in");
        def->connect("op0.out", "self.Y.0");
    };

    gen->setGeneratorDefFromFun(genFun);

  }
  
  Params muxParams = {{"WIDTH", c->Int()}};
  TypeGen* muxTP =
    rtLib->newTypeGen(
                      "rtMux",
                      muxParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                            {"A", c->BitIn()->Arr(width)},
                              {"B", c->BitIn()->Arr(width)},
                                {"S", c->BitIn()},
                                  {"Y",c->Bit()->Arr(width)}});
                      });

  rtLib->newGeneratorDecl("rtMux", muxTP, muxParams);

  auto muxGen = c->getGenerator("rtlil.rtMux");
  muxGen->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      uint width = args.at("WIDTH")->get<int>();

      Instance* mux = nullptr;
      //if (width > 1) {
        mux = def->addInstance("mux0", "coreir.mux", {{"width", Const::make(c, width)}});
        //} else {
        //mux = def->addInstance("mux0", "corebit.mux");
        //}

      assert(mux != nullptr);

      def->connect("self.A", "mux0.in0");
      def->connect("self.B", "mux0.in1");
      def->connect("self.S", "mux0.sel");
      def->connect("self.Y", "mux0.out");
    });

  // Sequential nodes
  Params dffParams = {{"WIDTH", c->Int()}, {"CLK_POLARITY", c->Bool()}};
  TypeGen* dffTP =
    rtLib->newTypeGen(
                      "dff",
                      dffParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                            {"CLK", c->BitIn()},
                              {"D", c->BitIn()->Arr(width)},
                                {"Q", c->Bit()->Arr(width)}});
                      });

  rtLib->newGeneratorDecl("dff", dffTP, dffParams);

  auto dffGen = c->getGenerator("rtlil.dff");
  dffGen->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      bool polarity = args.at("CLK_POLARITY")->get<bool>();

      ASSERT(polarity == true, "Currently CoreIR only supports rising edge DFFs");

      uint width = args.at("WIDTH")->get<int>();

      Instance* reg = nullptr;

      reg = def->addInstance("reg0",
                             "coreir.reg",
                             {{"width", Const::make(c, width)}});

      assert(reg != nullptr);

      def->connect("self.D", "reg0.in");

      // Add clock cast node, in rtlil the clock input is just another bit
      //def->addInstance("toClk0", "rtlil.to_clkIn");
      def->addInstance("toClk0",
                       "coreir.wrap",
                       {{"type", Const::make(c, c->Named("coreir.clk"))}});

      def->connect("self.CLK", "toClk0.in");
      def->connect("toClk0.out", "reg0.clk");

      def->connect("reg0.out", "self.Q");
    });

  Params adffParams =
    {{"WIDTH", c->Int()}, {"CLK_POLARITY", c->Bool()},
     // NOTE: ARST_VALUE should really be a bit vector
     {"ARST_POLARITY", c->Bool()}}; //, {"ARST_VALUE", c->BitVector()}};

  TypeGen* adffTP =
    rtLib->newTypeGen(
                      "adff",
                      adffParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                            {"CLK", c->BitIn()},
                              {"D", c->BitIn()->Arr(width)},
                                {"ARST", c->BitIn()},
                                  {"Q", c->Bit()->Arr(width)}});
                      });

  rtLib->newGeneratorDecl("adff", adffTP, adffParams);

  auto adffModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    uint width = genargs.at("WIDTH")->get<int>();
    modparams["init"] = BitVectorType::make(c,width);
    //defaultargs["init"] = Const::make(c,BitVector(width,0));
    return {modparams,defaultargs};
  };

  auto adffGen = c->getGenerator("rtlil.adff");
  adffGen->setModParamsGen(adffModParamFun);
  adffGen->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      bool polarity = args.at("CLK_POLARITY")->get<bool>();

      bool rstPolarity = args.at("ARST_POLARITY")->get<bool>();

      Module* mod = def->getModule();
      auto initVal = mod->getArg("init");

      uint width = args.at("WIDTH")->get<int>();

      Instance* reg = nullptr;

      reg = def->addInstance("reg0",
                             "coreir.reg_arst",
                             {{"width", Const::make(c, width)}},
                             {{"init", initVal},
                                 {"clk_posedge", Const::make(c, polarity)},
                                   {"arst_posedge", Const::make(c, rstPolarity)}});

      assert(reg != nullptr);

      def->connect("self.D", "reg0.in");

      // Add clock cast node, in rtlil the clock input is just another bit
      //def->addInstance("toClk0", "rtlil.to_clkIn");
      def->addInstance("toClk0",
                       "coreir.wrap",
                       {{"type", Const::make(c, c->Named("coreir.clk"))}});

      def->addInstance("toRST0",
                       "coreir.wrap",
                       {{"type", Const::make(c, c->Named("coreir.arst"))}});
      
      def->connect("self.ARST", "toRST0.in");
      def->connect("toRST0.out", "reg0.arst");
      def->connect("self.CLK", "toClk0.in");
      def->connect("toClk0.out", "reg0.clk");

      def->connect("reg0.out", "self.Q");
    });
  
  Params dlatchParams = {{"WIDTH", c->Int()}, {"EN_POLARITY", c->Bool()}};
  TypeGen* dlatchTP =
    rtLib->newTypeGen(
                      "dlatch",
                      dlatchParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                              {"D", c->BitIn()->Arr(width)},
                                {"EN", c->BitIn()},
                                  {"Q", c->Bit()->Arr(width)}});
                      });

  rtLib->newGeneratorDecl("dlatch", dlatchTP, dlatchParams);

  Params dffsrParams = {{"WIDTH", c->Int()},
                        {"CLR_POLARITY", c->Bool()},
                        {"SET_POLARITY", c->Bool()},
                        {"CLK_POLARITY", c->Bool()}};
  TypeGen* dffsrTP =
    rtLib->newTypeGen(
                      "dffsr",
                      dffsrParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                              {"D", c->BitIn()->Arr(width)},
                                {"CLK", c->BitIn()},
                                  {"CLR", c->BitIn()->Arr(width)},
                                    {"SET", c->BitIn()->Arr(width)},
                                      {"Q", c->Bit()->Arr(width)}});
                      });

  rtLib->newGeneratorDecl("dffsr", dffsrTP, dffsrParams);

  Params shiftxParams = {{"A_WIDTH", c->Int()},
                         {"A_SIGNED", c->Bool()},
                         {"B_WIDTH", c->Int()},
                         {"B_SIGNED", c->Bool()},
                         {"Y_WIDTH", c->Int()}};

  TypeGen* shiftxTP =
    rtLib->newTypeGen(
                      "shiftx",
                      shiftxParams,
                      [](Context* c, Values genargs) {
                        uint a_width = genargs.at("A_WIDTH")->get<int>();
                        uint b_width = genargs.at("B_WIDTH")->get<int>();
                        uint y_width = genargs.at("Y_WIDTH")->get<int>();

                        return c->Record({
                              {"A", c->BitIn()->Arr(a_width)},
                                {"B", c->BitIn()->Arr(b_width)},
                                  {"Y", c->Bit()->Arr(y_width)}});
                      });

  rtLib->newGeneratorDecl("shiftx", shiftxTP, shiftxParams);
  
  Params memParams =
    {{"SIZE", c->Int()}, {"WIDTH", c->Int()}};
  TypeGen* memTP =
    rtLib->newTypeGen("memory",
                      memParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();
                        uint depth = genargs.at("SIZE")->get<int>();
                        uint awidth = ceil(log2(depth));

                        return c->Record({
                            {"RD_EN", c->BitIn()},
                              {"RD_DATA", c->Bit()->Arr(width)},
                                {"RD_ADDR", c->BitIn()->Arr(awidth)},
                                  {"RD_CLK", c->BitIn()},
                                    {"WR_EN", c->BitIn()->Arr(width)},
                                      {"WR_DATA", c->BitIn()->Arr(width)},
                                        {"WR_ADDR", c->BitIn()->Arr(awidth)},
                                          {"WR_CLK", c->BitIn()}
                          });
                      });

  auto memGen = rtLib->newGeneratorDecl("memory", memTP, memParams);

  // TODO: Proper RD_EN, RD_CLK use
  memGen->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      int depth = args.at("SIZE")->get<int>();
      int width = args.at("WIDTH")->get<int>();

      def->addInstance("mem",
                       "coreir.mem",
                       {{"width", Const::make(c, width)},
                           {"depth", Const::make(c, depth)}});

      // Add clock cast node, in rtlil the clock input is just another bit
      //def->addInstance("toClk0", "rtlil.to_clkIn");
      def->addInstance("toClk0",
                       "coreir.wrap",
                       {{"type", Const::make(c, c->Named("coreir.clk"))}});

      def->connect("self.WR_CLK", "toClk0.in");
      def->connect("toClk0.out", "mem.clk");

      def->connect("self.RD_ADDR", "mem.raddr");
      // Correct this bitwise enable!
      def->connect("self.WR_EN.0", "mem.wen");

      def->connect("self.WR_DATA", "mem.wdata");
      def->connect("self.WR_ADDR", "mem.waddr");

      def->connect("mem.rdata", "self.RD_DATA");
    });
  
  // BitInOut conversion facilities
  Params outToInOutParams =
    {{"WIDTH", c->Int()}};
  TypeGen* outToInOutTP =
    rtLib->newTypeGen("outArrayToInOutArray",
                      outToInOutParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                            {"IN", c->BitIn()->Arr(width)},
                              {"OUT", c->BitInOut()->Arr(width)}
                          });
                      });

  rtLib->newGeneratorDecl("outArrayToInOutArray", outToInOutTP, outToInOutParams);

  Params inOutToOutParams =
    {{"WIDTH", c->Int()}};
  TypeGen* inOutToOutTP =
    rtLib->newTypeGen("inOutToOut",
                      outToInOutParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                            {"IN", c->BitInOut()->Arr(width)},
                              {"OUT", c->Bit()->Arr(width)}
                          });
                      });

  rtLib->newGeneratorDecl("inOutArrayToOutArray", inOutToOutTP, inOutToOutParams);

  Params padIOParams =
    {{"WIDTH", c->Int()}};
  TypeGen* padIOTP =
    rtLib->newTypeGen("padIO",
                      padIOParams,
                      [](Context* c, Values genargs) {
                        uint width = genargs.at("WIDTH")->get<int>();

                        return c->Record({
                            {"INOUT_PORT", c->BitInOut()->Arr(width)},
                              {"IN_PORT", c->BitIn()->Arr(width)},
                                {"OUT_PORT", c->Bit()->Arr(width)},
                                  {"INOUT_DRIVER_PORT", c->BitInOut()->Arr(width)}
                          });
                      });

  rtLib->newGeneratorDecl("padIO", padIOTP, padIOParams);

  Type* highImpedanceType =
    c->Record({{"OUT", c->Bit()}});
  rtLib->newModuleDecl("highImpedanceBit", highImpedanceType);

  Type* unknownBitType =
    c->Record({{"OUT", c->Bit()}});
  auto uMod = rtLib->newModuleDecl("unknownBit", unknownBitType);
  auto uDef = uMod->newModuleDef();

  uDef->addInstance("uConst",
                    "coreir.const",
                    {{"width", Const::make(c, 1)}},
                    {{"value", Const::make(c, BitVector(1, "x"))}});

  uDef->connect("uConst.out.0", "self.OUT");

  uMod->setDef(uDef);
  
  return rtLib;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(rtlil)
