#include "coreir/libs/rtlil.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(rtlil);

using namespace std;
using namespace CoreIR;

std::string rtlilCoreirName(const std::string& name) {
  //"logic_and", "logic_or", "eqx", "nex", "lt", "gt"};
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


  // Casting nodes
  Params extendParams = {{"in_width", c->Int()}, {"out_width", c->Int()}};
  TypeGen* extendTP =
    rtLib->newTypeGen("extend",
                      extendParams,
                      [](Context* c, Values genargs) {
                        uint in_width = genargs.at("in_width")->get<int>();
                        uint out_width = genargs.at("out_width")->get<int>();

                        ASSERT(in_width <= out_width, "in_width > out_width in extend node");

                        return c->Record({
                            {"in", c->BitIn()->Arr(in_width)},
                              {"out", c->Bit()->Arr(out_width)}
                          });
                      });

  rtLib->newGeneratorDecl("extend", extendTP, extendParams);

  Type* toClockType = c->Record({{"in", c->Bit()}, {"out", c->Named("coreir.clkIn")}});
  rtLib->newModuleDecl("to_clkIn", toClockType);

  // Operation related nodes
  vector<string> rtlilBinops{"and", "or", "xor", "xnor", "shl", "shr", "sshl", "sshr", "logic_and", "logic_or", "eqx", "nex", "lt", "le", "eq", "ne", "ge", "gt", "add", "sub", "mul", "div", "mod", "pow"};

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
  vector<string> rtlilBinaryComps{"logic_and", "logic_or", "eqx", "nex", "lt", "le", "eq", "ne", "ge", "gt"};
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

        ASSERT(!a_signed, "Have not yet added signed comparator support for RTLIL");
        ASSERT(!b_signed, "Have not yet added signed comparator support for RTLIL");

        uint ext_width = max(a_width, b_width);

        def->addInstance("extendA",
                         "rtlil.extend",
                         {{"in_width", Const::make(c, a_width)},
                             {"out_width", Const::make(c, ext_width)}});

        def->addInstance("extendB",
                         "rtlil.extend",
                         {{"in_width", Const::make(c, b_width)},
                             {"out_width", Const::make(c, ext_width)}});

        string opGenName = rtlilCoreirName(name);
        def->addInstance("op0", opGenName, {{"width", Const::make(c, ext_width)}});

        def->connect("self.A", "extendA.in");
        def->connect("self.B", "extendB.in");
        
        def->connect("extendA.out", "op0.in0");
        def->connect("extendB.out", "op0.in1");

        def->connect("op0.out", "self.Y");
    };

    gen->setGeneratorDefFromFun(genFun);

    //gen->setGeneratorDefFromFun(genFun);
    // [&name](Context* c, Values args, ModuleDef* def) {
    //     uint a_width = args.at("A_WIDTH")->get<int>();
    //     uint b_width = args.at("B_WIDTH")->get<int>();
    //     uint y_width = args.at("Y_WIDTH")->get<int>();

    //     ASSERT(y_width == 1, "Output of a comparator must be 1 bit!");

    //     bool a_signed = args.at("A_SIGNED")->get<bool>();
    //     bool b_signed = args.at("B_SIGNED")->get<bool>();

    //     ASSERT(!a_signed, "Have not yet added signed comparator support for RTLIL");
    //     ASSERT(!b_signed, "Have not yet added signed comparator support for RTLIL");

    //     uint ext_width = max(a_width, b_width);

    //     def->addInstance("extendA",
    //                      "rtlil.extend",
    //                      {{"in_width", Const::make(c, a_width)},
    //                          {"out_width", Const::make(c, ext_width)}});

    //     def->addInstance("extendB",
    //                      "rtlil.extend",
    //                      {{"in_width", Const::make(c, b_width)},
    //                          {"out_width", Const::make(c, ext_width)}});

    //     string opGenName = rtlilCoreirName(name);
    //     def->addInstance("op0", opGenName, {{"width", Const::make(c, ext_width)}});
        
    //     // def->connect("self.A", "mux0.in0");
    //     // def->connect("self.B", "mux0.in1");
    //     // def->connect("self.S", "mux0.sel");
    //     // def->connect("self.Y", "mux0.out");
    //   });

  }

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
      if (width > 1) {
        mux = def->addInstance("mux0", "coreir.mux", {{"width", Const::make(c, width)}});
      } else {
        mux = def->addInstance("mux0", "corebit.mux");
      }

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
      uint polarity = args.at("POLARITY")->get<int>();

      ASSERT(polarity == 1, "Currently CoreIR only supports rising edge DFFs");

      uint width = args.at("WIDTH")->get<int>();

      Instance* reg = nullptr;

      if (width == 1) {
        reg = def->addInstance("reg0", "corebit.dff");
      } else {
        reg = def->addInstance("reg0",
                               "coreir.reg",
                               {{"width", Const::make(c, width)}});
      }

      assert(reg != nullptr);

      def->connect("self.D", "reg0.in");

      // Add clock cast node, in rtlil the clock input is just another bit
      def->addInstance("toClk0", "rtlil.to_clkIn");

      def->connect("self.CLK", "toClk0.in");
      def->connect("toClk0.out", "reg0.clk");

      def->connect("reg0.out", "self.Q");
    });

  Params adffParams = {{"WIDTH", c->Int()}, {"CLK_POLARITY", c->Bool()},
                       // NOTE: ARST_VALUE should really be a bit vector
                       {"ARST_POLARITY", c->Bool()}, {"ARST_VALUE", c->Int()}};
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
  
  return rtLib;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(rtlil)
