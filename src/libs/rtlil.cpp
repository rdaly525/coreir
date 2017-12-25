#include "coreir/libs/rtlil.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(rtlil);

using namespace std;
using namespace CoreIR;

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
