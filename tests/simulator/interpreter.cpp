#include "catch.hpp"

#include "coreir.h"
#include "coreir/libs/commonlib.h"
#include "coreir/libs/float.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/simulator/interpreter.h"

#include "fuzzing.hpp"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

string quote(string s) { return "\"" + s + "\""; }

void addCounter(Context* c, Namespace* global) {

  // assert(false);
  Params counterParams = {{"width", c->Int()}};

  TypeGen* counterTypeGen = global->newTypeGen(
    "myCounterTypeGen",
    counterParams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      return c->Record({
        {"en", c->BitIn()},
        {"out", c->Array(width, c->Bit())},
        {"clk", c->Named("coreir.clkIn")},
      });
    }  // end lambda
  );   // end newTypeGen

  ASSERT(
    global->hasTypeGen("myCounterTypeGen"),
    "Can check for typegens in namespaces");

  Generator* counter = global->newGeneratorDecl(
    "myCounter",
    counterTypeGen,
    counterParams);

  counter->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();

    Values wArg({{"width", Const::make(c, width)}});
    def->addInstance("ai", "coreir.add", wArg);
    def->addInstance(
      "ci",
      "coreir.const",
      wArg,
      {{"value", Const::make(c, BitVector(width, 1))}});

    def->addInstance(
      "ri",
      "mantle.reg",
      {{"width", Const::make(c, width)}, {"has_en", Const::make(c, true)}});

    def->connect("self.clk", "ri.clk");
    def->connect("self.en", "ri.en");
    def->connect("ci.out", "ai.in0");
    def->connect("ai.out", "ri.in");
    def->connect("ri.out", "ai.in1");
    def->connect("ri.out", "self.out");
  });  // end lambda, end function
}

TEST_CASE("Implementing divide") {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  uint width = 16;
  Type* tp = c->Record({{"in0", c->BitIn()->Arr(width)},
                        {"in1", c->BitIn()->Arr(width)},
                        {"out", c->Bit()->Arr(width)}});

  Module* mod = g->newModuleDecl("div_test", tp);
  ModuleDef* def = mod->newModuleDef();

  def->addInstance("c0", "coreir.udiv", {{"width", Const::make(c, width)}});
  def->connect("self.in0", "c0.in0");
  def->connect("self.in1", "c0.in1");
  def->connect("c0.out", "self.out");
  mod->setDef(def);

  c->runPasses({"rungenerators"});

  SimulatorState state(mod);
  state.setValue("self.in0", BitVector(width, 182));
  state.setValue("self.in1", BitVector(width, 13));
  state.execute();

  cout << "Divide output = " << state.getBitVec("self.out") << endl;

  REQUIRE(state.getBitVec("self.out") == BitVector(width, 182 / 13));
}

TEST_CASE("Checking concat order") {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  uint width0 = 12;
  uint width1 = 18;
  Type* tp = c->Record({{"in0", c->BitIn()->Arr(width0)},
                        {"in1", c->BitIn()->Arr(width1)},
                        {"out", c->Bit()->Arr(width1 + width0)}});

  Module* mod = g->newModuleDecl("concat_test", tp);
  ModuleDef* def = mod->newModuleDef();

  def->addInstance(
    "c0",
    "coreir.concat",
    {{"width0", Const::make(c, width0)}, {"width1", Const::make(c, width1)}});
  def->connect("self.in0", "c0.in0");
  def->connect("self.in1", "c0.in1");
  def->connect("c0.out", "self.out");
  mod->setDef(def);

  c->runPasses({"rungenerators"});

  SimulatorState state(mod);
  state.setValue("self.in0", BitVector(width0, 1));
  state.setValue("self.in1", BitVector(width1, 0));
  state.execute();

  cout << "Concat output = " << state.getBitVec("self.out") << endl;

  REQUIRE(state.getBitVec("self.out").bitLength() == (width0 + width1));
  // LSB is from in0
  REQUIRE(state.getBitVec("self.out").get(0) == BitVector(1, 1).get(0));
  // MSB is from in1
  REQUIRE(state.getBitVec("self.out").get(width0) == BitVector(1, 0).get(0));
}

TEST_CASE("Interpreting coreir.wire and corebit.wire") {

  Context* c = newContext();
  Namespace* g = c->getGlobal();

  SECTION("coreir.wire") {
    uint width = 4;
    Type* tp = c->Record(
      {{"in", c->BitIn()->Arr(width)}, {"out", c->Bit()->Arr(width)}});

    Module* mod = g->newModuleDecl("md", tp);
    ModuleDef* def = mod->newModuleDef();
    def->addInstance("w", "coreir.wire", {{"width", Const::make(c, width)}});
    def->connect("self.in", "w.in");
    def->connect("w.out", "self.out");
    mod->setDef(def);

    c->runPasses({"rungenerators"});

    SimulatorState state(mod);
    state.setValue("self.in", BitVector(width, 12));
    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 12));
  }

  SECTION("corebit.wire") {
    Type* tp = c->Record({{"in", c->BitIn()}, {"out", c->Bit()}});

    Module* mod = g->newModuleDecl("md", tp);
    ModuleDef* def = mod->newModuleDef();
    def->addInstance("w", "corebit.wire");
    def->connect("self.in", "w.in");
    def->connect("w.out", "self.out");
    mod->setDef(def);

    c->runPasses({"rungenerators"});

    SimulatorState state(mod);
    state.setValue("self.in", BitVector(1, 12));
    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(1, 12));
  }

  deleteContext(c);
}

TEST_CASE("Interpreting coreir.term and corebit.term") {

  Context* c = newContext();
  Namespace* g = c->getGlobal();

  SECTION("coreir.term") {
    uint width = 4;
    Type* tp = c->Record(
      {{"in", c->BitIn()->Arr(width)}, {"out", c->Bit()->Arr(width)}});

    Module* mod = g->newModuleDecl("md", tp);
    ModuleDef* def = mod->newModuleDef();

    def->addInstance("w", "coreir.term", {{"width", Const::make(c, width)}});
    def->connect("self.in", "w.in");

    def->addInstance(
      "c",
      "coreir.const",
      {{"width", Const::make(c, width)}},
      {{"value", Const::make(c, BitVector(width, 1))}});
    def->connect("c.out", "self.out");

    mod->setDef(def);

    c->runPasses({"rungenerators"});

    SimulatorState state(mod);
    state.setValue("self.in", BitVector(width, 12));
    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 1));
  }

  SECTION("corebit.term") {
    Type* tp = c->Record({{"in", c->BitIn()}, {"out", c->Bit()}});

    Module* mod = g->newModuleDecl("md", tp);
    ModuleDef* def = mod->newModuleDef();

    def->addInstance("w", "corebit.term");
    def->connect("self.in", "w.in");

    def->addInstance("c", "corebit.const", {{"value", Const::make(c, false)}});
    def->connect("c.out", "self.out");

    mod->setDef(def);

    c->runPasses({"rungenerators"});

    SimulatorState state(mod);
    state.setValue("self.in", BitVector(1, 1));
    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(1, 0));
  }

  deleteContext(c);
}

TEST_CASE("Interpreting circuits with combinational loops") {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  SECTION("Two muxes") {

    // uint width = 2;

    // Type* twoMuxType =
    //   c->Record({
    //       {"in", c->BitIn()->Arr(width)},
    //         {"sel", c->BitIn()},
    //           {"out", c->Bit()->Arr(width)}
    //     });

    // Module* twoMux = c->getGlobal()->newModuleDecl("twoMux", twoMuxType);
    // ModuleDef* def = twoMux->newModuleDef();

    // def->addInstance("mux0",
    //                  "coreir.mux",
    //                  {{"width", Const::make(c, width)}});

    // def->connect("self.sel", "mux0.sel");
    // def->connect("self.in", "mux0.in0");
    // def->connect("mux0.out", "mux0.in1");
    // def->connect("mux0.out", "self.out");

    // twoMux->setDef(def);

    // c->runPasses({"rungenerators", "flatten", "flattentypes",
    // "wireclocks-clk"});

    // SimulatorState state(twoMux);
    // state.setValue("self.sel", BitVector(1, 0));
    // state.setValue("self.in", BitVector(width, "11"));

    // state.execute();

    // REQUIRE(state.getBitVec("self.out") == BitVector(width, "11"));
  }

  deleteContext(c);
}

TEST_CASE("Run 32 bit float add") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()->Arr(width)}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "add0",
    "float.add",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("add0.in0", "self.in0");
  def->connect("add0.in1", "self.in1");
  def->connect("add0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("0 + 0 == 0") {
    state.setValue("self.in0", BitVector(width, 0));
    state.setValue("self.in1", BitVector(width, 0));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 0));
  }

  SECTION("1.73 + 2.34") {
    float a = 1.73;
    float b = 2.34;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a)));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b)));

    state.execute();

    REQUIRE(
      state.getBitVec("self.out") == BitVector(width, bitCastToInt(a + b)));
  }
}

TEST_CASE("Run 16 bit float div") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 7;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()->Arr(width)}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "add0",
    "float.div",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("add0.in0", "self.in0");
  def->connect("add0.in1", "self.in1");
  def->connect("add0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("22.0 / PI") {
    float a = 22.0;
    float b = 3.14159;

    cout << "Float div = " << (a / b) << endl;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a) >> 16));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b) >> 16));

    state.execute();

    BitVector res(16, "0100000011100000");

    cout << "result as float = " << bitCastToFloat(res.to_type<int>() << 16)
         << endl;
    REQUIRE(state.getBitVec("self.out") == res);
  }

  SECTION("3.17187 / PI") {
    float a = 3.17187;
    float b = 3.14159;

    cout << "Float div = " << (a / b) << endl;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a) >> 16));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b) >> 16));

    state.execute();

    BitVector res("16'h3f81");

    cout << "result as float = " << bitCastToFloat(res.to_type<int>() << 16)
         << endl;
    REQUIRE(state.getBitVec("self.out") == res);
  }

  SECTION("0.0352941 / PI") {
    float a = 0.0352941;
    float b = 3.14159;

    cout << "Float div = " << (a / b) << endl;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a) >> 16));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b) >> 16));

    state.execute();

    BitVector res("16'h3c37");

    cout << "result as float = " << bitCastToFloat(res.to_type<int>() << 16)
         << endl;
    REQUIRE(state.getBitVec("self.out") == res);
  }
}

TEST_CASE("Run 32 bit float mul") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()->Arr(width)}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.mul",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("0 + 0 == 0") {
    state.setValue("self.in0", BitVector(width, 0));
    state.setValue("self.in1", BitVector(width, 0));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 0));
  }

  SECTION("1.73 * 2.34") {
    float a = 1.73;
    float b = 2.34;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a)));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b)));

    state.execute();

    REQUIRE(
      state.getBitVec("self.out") == BitVector(width, bitCastToInt(a * b)));
  }
}

TEST_CASE("Floating point gt") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.gt",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("27.0 > 9.4") {
    float a = 27.0;
    float b = 9.4;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a)));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b)));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(1, 1));
  }
}

TEST_CASE("Floating point ge") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.ge",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("!(-1.2 >= 0.4)") {
    float a = -1.2;
    float b = 0.4;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a)));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b)));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(1, 0));
  }
}

TEST_CASE("Floating point lt") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.lt",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("27.0 < 9.4") {
    float a = 27.0;
    float b = 9.4;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a)));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b)));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(1, 0));
  }
}

TEST_CASE("Floating point le") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.le",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("-1.2 <= 0.4") {
    float a = -1.2;
    float b = 0.4;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a)));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b)));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(1, 1));
  }
}

TEST_CASE("16 bit bfloat multiply") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 7;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()->Arr(width)}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.mul",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("0 * 0 == 0") {
    state.setValue("self.in0", BitVector(width, 0));
    state.setValue("self.in1", BitVector(width, 0));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 0));
  }

  SECTION("3.140625 * 7 == 22") {
    float a = 3.140625;
    float b = 7.0;
    float res = 22.0;
    auto a_bv = BitVector(width, bitCastToInt(a) >> 16);
    auto b_bv = BitVector(width, bitCastToInt(b) >> 16);
    auto res_bv = BitVector(width, bitCastToInt(res) >> 16);
    state.setValue("self.in0", a_bv);
    state.setValue("self.in1", b_bv);
    state.execute();
    REQUIRE(state.getBitVec("self.out") == res_bv);
  }
}

TEST_CASE("32 bit bfloat sub") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()->Arr(width)}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.sub",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("0 - 0 == 0") {
    state.setValue("self.in0", BitVector(width, 0));
    state.setValue("self.in1", BitVector(width, 0));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 0));
  }

  SECTION("7.0 - 9.7") {
    float a = 7.0;
    float b = 9.7;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a)));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b)));

    state.execute();

    float res = a - b;
    BitVector expectedFp = BitVector(width, bitCastToInt(a - b));
    cout << "Expected fsub     = " << expectedFp << endl;
    cout << "Actual fsub       = " << state.getBitVec("self.out") << endl;
    REQUIRE(state.getBitVec("self.out") == expectedFp);
  }
}

TEST_CASE("16 bit bfloat sub") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 7;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record({{"in0", c->BitIn()->Arr(width)},
                              {"in1", c->BitIn()->Arr(width)},
                              {"out", c->Bit()->Arr(width)}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.sub",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in0", "self.in0");
  def->connect("mul0.in1", "self.in1");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("0 - 0 == 0") {
    state.setValue("self.in0", BitVector(width, 0));
    state.setValue("self.in1", BitVector(width, 0));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 0));
  }

  SECTION("7.0 - 9.7") {
    float a = 7.0;
    float b = 9.7;

    state.setValue("self.in0", BitVector(width, bitCastToInt(a) >> 16));
    state.setValue("self.in1", BitVector(width, bitCastToInt(b) >> 16));

    state.execute();

    float res = a - b;
    BitVector expectedFp = BitVector(width, bitCastToInt(a - b) >> 16);
    cout << "Expected fsub     = " << expectedFp << endl;
    cout << "Actual fsub       = " << state.getBitVec("self.out") << endl;
    REQUIRE(state.getBitVec("self.out") == expectedFp);
  }
}

TEST_CASE("32 bit negate") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  CoreIRLoadLibrary_float(c);

  int expBits = 8;
  int fracBits = 23;
  int width = 1 + expBits + fracBits;

  Type* faddType = c->Record(
    {{"in", c->BitIn()->Arr(width)}, {"out", c->Bit()->Arr(width)}});

  Module* faddM = c->getGlobal()->newModuleDecl("faddM", faddType);
  ModuleDef* def = faddM->newModuleDef();

  def->addInstance(
    "mul0",
    "float.neg",
    {{"exp_bits", Const::make(c, expBits)},
     {"frac_bits", Const::make(c, fracBits)}});

  def->connect("mul0.in", "self.in");
  def->connect("mul0.out", "self.out");
  faddM->setDef(def);

  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  SimulatorState state(faddM);

  SECTION("-(12.7) == -12.7") {
    float a = 12.7;
    state.setValue("self.in", BitVector(width, bitCastToInt(a)));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, bitCastToInt(-a)));
  }
}

// Define unified buffer generator simulation class
class UnifiedBufferStub : public SimulatorPlugin {
  BitVector lastVal;

  int width;

 public:
  void initialize(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);
    Wireable* w = wd.getWire();

    assert(isInstance(w));

    Instance* inst = toInstance(w);
    width = inst->getModuleRef()->getGenArgs().at("width")->get<int>();
    lastVal = BitVector(width, 0);
  }

  void exeSequential(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);

    simState.updateInputs(vd);

    assert(isInstance(wd.getWire()));

    Instance* inst = toInstance(wd.getWire());

    auto inSels = getInputSelects(inst);

    Select* arg1 = toSelect(CoreIR::findSelect("in", inSels));
    assert(arg1 != nullptr);

    lastVal = simState.getBitVec(arg1);
  }

  void exeCombinational(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    simState.setValue(toSelect(inst->sel("out")), lastVal);
  }
};

TEST_CASE("Unified buffer simulation stub") {
  std::cout << "unified buffer sim stub running...\n";
  Context* c = newContext();
  Namespace* g = c->newNamespace("bufferLib");

  // Define (dummy) unified buffer generator
  Params params = {{"width", c->Int()}, {"depth", c->Int()}};
  auto ubufstubTg = g->newTypeGen(
    "ubufstub_type",
    params,
    [](Context* c, Values genargs) {
      uint width = genargs.at("width")->get<int>();
      uint depth = genargs.at("depth")->get<int>();

      return c->Record({{"clk", c->Named("coreir.clkIn")},
                        {"in", c->BitIn()->Arr(width)},
                        {"out", c->Bit()->Arr(width)}});
    });

  g->newGeneratorDecl("ubufstub", ubufstubTg, params);

  // Build container module
  Namespace* global = c->getNamespace("global");
  int width = 16;
  Type* bufWrapperType = c->Record({{"clk", c->Named("coreir.clkIn")},
                                    {"in", c->BitIn()->Arr(width)},
                                    {"out", c->Bit()->Arr(width)}});

  Module* wrapperMod = c->getGlobal()->newModuleDecl(
    "bufWrapper",
    bufWrapperType);
  ModuleDef* def = wrapperMod->newModuleDef();

  def->addInstance(
    "buf0",
    "bufferLib.ubufstub",
    {{"width", Const::make(c, width)}, {"depth", Const::make(c, 64)}});

  def->connect("buf0.out", "self.out");
  def->connect("buf0.in", "self.in");
  def->connect("buf0.clk", "self.clk");

  wrapperMod->setDef(def);
  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  // Build the simulator with the new model
  auto modBuilder = [](WireNode& wd) {
    UnifiedBufferStub* simModel = new UnifiedBufferStub();
    return simModel;
  };

  map<std::string, SimModelBuilder> qualifiedNamesToSimPlugins{
    {string("bufferLib.ubufstub"), modBuilder}};

  SimulatorState state(wrapperMod, qualifiedNamesToSimPlugins);

  state.setValue("self.in", BitVector(width, 89));
  state.setClock("self.clk", 0, 1);

  state.resetCircuit();

  state.execute();

  REQUIRE(state.getBitVec("self.out") == BitVector(width, 89));

  state.setValue("self.in", BitVector(width, 7));

  state.execute();

  REQUIRE(state.getBitVec("self.out") == BitVector(width, 7));

  deleteContext(c);
  std::cout << "PASSED: unified buffer stub simulation!\n";
}

// Define address generator simulation class
class UnifiedBufferAddressGenerator : public SimulatorPlugin {
  int width;
  vector<int> iter_list;

  vector<int> output_range;
  vector<int> output_stride;
  vector<int> output_start;

  size_t dimension;
  size_t port;
  int total_iter;
  bool is_done;

  vector<int> get_dims(Type* type) {
    vector<int> lengths;
    uint bitwidth = 1;
    Type* cType = type;
    while (!cType->isBaseType()) {
      if (auto aType = dyn_cast<ArrayType>(cType)) {

        uint length = aType->getLen();

        cType = aType->getElemType();
        if (cType->isBaseType()) { bitwidth = length; }
        else {
          lengths.insert(lengths.begin(), length);
          // lengths.push_back(length);
        }
      }
    }

    lengths.insert(lengths.begin(), bitwidth);
    return lengths;
  }

 public:
  UnifiedBufferAddressGenerator() { is_done = false; }

  UnifiedBufferAddressGenerator(
    vector<int> range,
    vector<int> stride,
    vector<int> start,
    int myWidth)
      : is_done(false) {
    init_parameters(myWidth, range, stride, start);
  }

  bool isDone() { return is_done; }

  void restart() {
    is_done = false;
    for (auto& iter : iter_list) { iter = 0; }
  }

  void updateIterator(BitVector resetVal) {
    if (resetVal == BitVector(1, 1)) {
      restart();
      return;
    }

    // logic to update the internal iterator
    for (size_t dim = 0; dim < dimension; dim++) {
      iter_list[dim] += 1;

      // return to zero for the previous dim if we enter the next dim
      if (dim > 0) iter_list[dim - 1] = 0;

      // not the last dimension
      if (dim < dimension - 1) {
        if (iter_list[dim] < output_range[dim]) {
          is_done = false;
          break;
        }
      }
      else {
        if (iter_list[dim] == output_range[dim]) {
          is_done = true;
          break;
        }
      }
    }
  }

  int calcBaseAddress() {
    std::cout << "dims=" << dimension << std::endl;
    int addr_offset = 0;
    assert(iter_list.size() <= dimension);
    assert(output_stride.size() <= dimension);
    for (size_t i = 0; i < dimension; i++) {
      addr_offset += iter_list.at(i) * output_stride.at(i);
    }
    return addr_offset;
  }

  vector<int> getAddresses() {
    vector<int> addresses = vector<int>(output_start.size());
    auto baseAddr = calcBaseAddress();

    for (size_t i = 0; i < addresses.size(); ++i) {
      addresses.at(i) = baseAddr + output_start.at(i);
    }

    return addresses;
  }

  void init_parameters(
    int _width,
    vector<int> _output_range,
    vector<int> _output_stride,
    vector<int> _output_start) {
    width = _width;
    output_range = _output_range;
    output_stride = _output_stride;
    output_start = _output_start;

    // start values all need to decrement 1
    for (auto& start_num : output_start) { start_num -= 1; }

    // deduce from other parameters
    assert(output_range.size() == output_stride.size());
    dimension = output_range.size();
    std::cout << "buffer has " << dimension << " dims\n";
    port = output_start.size();
    total_iter = 1;

    for (size_t i = 0; i < dimension; ++i) {
      total_iter *= output_range.at(i) / output_stride.at(i);
    }

    // initialize parameters
    iter_list = vector<int>(dimension);
    assert(iter_list.size() == dimension);
    restart();
  }

  void initialize(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);
    Wireable* w = wd.getWire();

    assert(isInstance(w));

    // extract parameters
    Instance* inst = toInstance(w);
    auto myWidth = inst->getModuleRef()->getGenArgs().at("width")->get<int>();
    auto rangeType = inst->getModuleRef()
                       ->getGenArgs()
                       .at("range_type")
                       ->get<Type*>();
    auto strideType = inst->getModuleRef()
                        ->getGenArgs()
                        .at("stride_type")
                        ->get<Type*>();
    auto startType = inst->getModuleRef()
                       ->getGenArgs()
                       .at("start_type")
                       ->get<Type*>();

    init_parameters(
      myWidth,
      get_dims(rangeType),
      get_dims(strideType),
      get_dims(startType));
  }

  void exeSequential(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);

    simState.updateInputs(vd);

    assert(isInstance(wd.getWire()));

    Instance* inst = toInstance(wd.getWire());

    auto inSels = getInputSelects(inst);

    Select* arg1 = toSelect(CoreIR::findSelect("reset", inSels));
    assert(arg1 != nullptr);
    BitVector resetVal = simState.getBitVec(arg1);

    updateIterator(resetVal);
  }

  void exeCombinational(vdisc vd, SimulatorState& simState) {
    std::cout << "execomb..\n";
    auto wd = simState.getCircuitGraph().getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    int addr_offset = calcBaseAddress();
    simState.setValue(
      toSelect(inst->sel("out")),
      BitVector(width, addr_offset));
  }
};

TEST_CASE("Unified buffer address generator simulation") {
  std::cout << "unified buffer address generator sim running...\n";
  Context* c = newContext();
  Namespace* g = c->newNamespace("bufferLib");

  // Define unified buffer address generator
  Params params = {{"width", c->Int()},
                   {"range_type", CoreIRType::make(c)},
                   {"stride_type", CoreIRType::make(c)},
                   {"start_type", CoreIRType::make(c)}};
  auto uBufAddrTg = g->newTypeGen(
    "ubufaddrgen_type",
    params,
    [](Context* c, Values genargs) {
      uint width = genargs.at("width")->get<int>();

      return c->Record({{"clk", c->Named("coreir.clkIn")},
                        {"reset", c->BitIn()},
                        {"out", c->Bit()->Arr(width)}});
    });

  g->newGeneratorDecl("ubufaddr", uBufAddrTg, params);

  // Build container module
  Namespace* global = c->getNamespace("global");
  int width = 16;
  Type* bufaddrWrapperType = c->Record({{"clk", c->Named("coreir.clkIn")},
                                        {"reset", c->BitIn()},
                                        {"out", c->Bit()->Arr(width)}});

  Module* wrapperMod = c->getGlobal()->newModuleDecl(
    "bufaddrWrapper",
    bufaddrWrapperType);
  ModuleDef* def = wrapperMod->newModuleDef();

  def->addInstance(
    "bufaddr0",
    "bufferLib.ubufaddr",
    {{"width", Const::make(c, width)},
     {"range_type", Const::make(c, c->Bit()->Arr(6)->Arr(3)->Arr(32)->Arr(32))},
     {"stride_type",
      Const::make(c, c->Bit()->Arr(4)->Arr(272)->Arr(8)->Arr(272))},
     {"start_type", Const::make(c, c->Bit()->Arr(0)->Arr(2)->Arr(3)->Arr(4))}});

  def->connect("bufaddr0.out", "self.out");
  def->connect("bufaddr0.reset", "self.reset");
  def->connect("bufaddr0.clk", "self.clk");

  wrapperMod->setDef(def);
  c->runPasses(
    {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

  // Build the simulator with the new model
  auto modBuilder = [](WireNode& wd) {
    UnifiedBufferAddressGenerator*
      simModel = new UnifiedBufferAddressGenerator();
    return simModel;
  };

  map<std::string, SimModelBuilder> qualifiedNamesToSimPlugins{
    {string("bufferLib.ubufaddr"), modBuilder}};

  SimulatorState state(wrapperMod, qualifiedNamesToSimPlugins);

  state.setValue("self.reset", BitVector(1, 1));
  state.setClock("self.clk", 0, 1);

  state.resetCircuit();

  state.execute();

  REQUIRE(state.getBitVec("self.out") == BitVector(width, 0));

  state.setValue("self.reset", BitVector(1, 0));

  state.execute();

  REQUIRE(state.getBitVec("self.out") == BitVector(width, 4));

  deleteContext(c);
  std::cout << "PASSED: unified buffer address generator simulation!\n";
}

// Define address generator simulation class
class UnifiedBuffer : public SimulatorPlugin {
  // int input_port;
  // int output_port;
  int capacity;
  int select;
  int width;

  UnifiedBufferAddressGenerator write_iterator;
  UnifiedBufferAddressGenerator read_iterator;
  vector<vector<int>> data;

  vector<int> get_dims(Type* type) {
    vector<int> lengths;
    uint bitwidth = 1;
    Type* cType = type;
    while (!cType->isBaseType()) {
      if (auto aType = dyn_cast<ArrayType>(cType)) {

        uint length = aType->getLen();

        cType = aType->getElemType();
        if (cType->isBaseType()) { bitwidth = length; }
        else {
          lengths.insert(lengths.begin(), length);
          // lengths.push_back(length);
        }
      }
    }

    lengths.insert(lengths.begin(), bitwidth);
    return lengths;
  }

 public:
  void initialize(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);
    Wireable* w = wd.getWire();

    assert(isInstance(w));

    // extract parameters
    Instance* inst = toInstance(w);
    width = inst->getModuleRef()->getGenArgs().at("width")->get<int>();
    auto outputRangeType = inst->getModuleRef()
                             ->getGenArgs()
                             .at("output_range_type")
                             ->get<Type*>();
    auto outputStrideType = inst->getModuleRef()
                              ->getGenArgs()
                              .at("output_stride_type")
                              ->get<Type*>();
    auto outputStartType = inst->getModuleRef()
                             ->getGenArgs()
                             .at("output_start_type")
                             ->get<Type*>();

    auto inputRangeType = inst->getModuleRef()
                            ->getGenArgs()
                            .at("input_range_type")
                            ->get<Type*>();
    auto inputStrideType = inst->getModuleRef()
                             ->getGenArgs()
                             .at("input_stride_type")
                             ->get<Type*>();
    auto inputStartType = inst->getModuleRef()
                            ->getGenArgs()
                            .at("input_start_type")
                            ->get<Type*>();

    auto output_range = get_dims(outputRangeType);
    auto output_stride = get_dims(outputStrideType);
    auto output_start = get_dims(outputStartType);

    write_iterator = UnifiedBufferAddressGenerator(
      get_dims(inputRangeType),
      get_dims(inputRangeType),
      get_dims(inputStartType),
      width);
    read_iterator = UnifiedBufferAddressGenerator(
      get_dims(outputRangeType),
      get_dims(outputStrideType),
      get_dims(outputStartType),
      width);

    // deduce capacity from other output iterator
    capacity = 1;
    size_t dimension = output_range.size();

    for (size_t i = 0; i < dimension; ++i) {
      capacity += (output_range.at(i) - 1) * max(output_stride.at(i), 0);
    }

    int max_start = 0;
    for (const auto& start_value : output_start) {
      max_start = max(max_start, start_value);
    }
    capacity += max_start;

    // initialize data and select
    data = vector<vector<int>>(2, vector<int>(capacity, 0));
    select = 0;
  }

  void switch_check() {
    if (write_iterator.isDone() && read_iterator.isDone()) {
      select = select ^ 1;
      read_iterator.restart();
      write_iterator.restart();
    }
  }

  void exeSequential(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);

    simState.updateInputs(vd);

    assert(isInstance(wd.getWire()));

    Instance* inst = toInstance(wd.getWire());

    auto inSels = getInputSelects(inst);

    Select* arg1 = toSelect(CoreIR::findSelect("reset", inSels));
    Select* arg2 = toSelect(CoreIR::findSelect("datain", inSels));
    assert(arg1 != nullptr);
    BitVector resetVal = simState.getBitVec(arg1);
    // auto in_data = simState.getBitVec(arg2);

    assert((!write_iterator.isDone()) && "No more write allowed.\n");
    write_iterator.updateIterator(resetVal);

    auto write_addr_array = write_iterator.getAddresses();
    // assert((write_addr_array.size() == in_data.size()) && "Input data width
    // not equals to port width.\n");
    for (size_t i = 0; i < write_addr_array.size(); i++) {
      int write_addr = write_addr_array[i];
      auto in_data = simState.getBitVec(arg2->sel(i));
      data[0x1 ^ select][write_addr] = in_data.to_type<int>();
    }

    switch_check();
  }

  void exeCombinational(vdisc vd, SimulatorState& simState) {
    auto wd = simState.getCircuitGraph().getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    assert((!read_iterator.isDone()) && "No more read allowed.\n");
    read_iterator.updateIterator(BitVector(1, 0));

    vector<int> out_data;
    for (auto read_addr : read_iterator.getAddresses()) {
      out_data.push_back(data[select][read_addr]);
    }

    switch_check();

    for (size_t i = 0; i < out_data.size(); ++i) {
      simState.setValue(
        toSelect(inst->sel("dataout")->sel(i)),
        BitVector(width, out_data.at(i)));
    }
  }
};

/*
  TEST_CASE("Unified buffer simulation") {
    std::cout << "unified buffer address generator sim running...\n";
    Context* c = newContext();
    Namespace* g = c->newNamespace("bufferLib");
    CoreIRLoadLibrary_commonlib(c);

    // Define unified buffer generator
    Params params =
      {{"width", c->Int()},
       {"range_type", CoreIRType::make(c)},
       {"stride_type", CoreIRType::make(c)},
       {"start_type", CoreIRType::make(c)}
      };
    auto uBufTg = g->newTypeGen(
                  "ubufgen_type",
                  params,
                  [](Context* c, Values genargs) {
                    uint width = genargs.at("width")->get<int>();

                    return c->Record({
                        {"clk",c->Named("coreir.clkIn")},
                        {"reset", c->BitIn()},
                        {"out", c->Bit()->Arr(width)}});
                  }
                  );

    g->newGeneratorDecl("ubuf", uBufTg, params);

    // Build container module
    Namespace* global = c->getNamespace("global");
    int width = 16;
    Type* bufWrapperType =
        c->Record({
            {"clk",c->Named("coreir.clkIn")},
            {"reset",c->BitIn()},
            {"out",c->Bit()->Arr(width)}
          });

    Module* wrapperMod =
      c->getGlobal()->newModuleDecl("bufWrapper", bufWrapperType);
    ModuleDef* def = wrapperMod->newModuleDef();

    def->addInstance("buf0",
                       "bufferLib.ubuf",
                       {{"width",       Const::make(c, width)},
                        {"range_type",  Const::make(c,
  c->Bit()->Arr(6)->Arr(3)->Arr(32)->Arr(32))},
                        {"stride_type", Const::make(c,
  c->Bit()->Arr(4)->Arr(272)->Arr(8)->Arr(272))},
                        {"start_type",  Const::make(c,
  c->Bit()->Arr(0)->Arr(2)->Arr(3)->Arr(4))}
                     });

    def->connect("buf0.out", "self.out");
    def->connect("buf0.reset", "self.reset");
    def->connect("buf0.clk", "self.clk");

    wrapperMod->setDef(def);
    c->runPasses({"rungenerators", "flatten", "flattentypes",
  "wireclocks-clk"});

    // Build the simulator with the new model
    auto modBuilder = [](WireNode& wd) {
      UnifiedBuffer* simModel = new UnifiedBuffer();
      return simModel;
    };

    map<std::string, SimModelBuilder>
  qualifiedNamesToSimPlugins{{string("bufferLib.ubuf"), modBuilder}};

    SimulatorState state(wrapperMod, qualifiedNamesToSimPlugins);

    state.setValue("self.reset", BitVector(1, 1));
    state.setClock("self.clk", 0, 1);

    state.resetCircuit();

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 0));

    state.setValue("self.reset", BitVector(1, 0));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(width, 4));

    deleteContext(c);
    std::cout << "PASSED: unified buffer simulation!\n";
  }
*/

TEST_CASE("Interpret simulator graphs") {

  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  SECTION("commonlib mux with 71 inputs") {
    uint N = 71;
    uint width = 16;

    CoreIRLoadLibrary_commonlib(c);

    Type* muxNType = c->Record(
      {{"in",
        c->Record({{"data", c->BitIn()->Arr(width)->Arr(N)},
                   {"sel", c->BitIn()->Arr(7)}})},
       {"out", c->Bit()->Arr(width)}});

    Module* muxNTest = c->getGlobal()->newModuleDecl("muxN", muxNType);
    ModuleDef* def = muxNTest->newModuleDef();

    def->addInstance(
      "mux0",
      "commonlib.muxn",
      {{"width", Const::make(c, width)}, {"N", Const::make(c, N)}});

    def->connect("mux0.out", "self.out");

    def->connect({"self", "in", "sel"}, {"mux0", "in", "sel"});
    for (uint i = 0; i < N; i++) {
      def->connect(
        {"self", "in", "data", to_string(i)},
        {"mux0", "in", "data", to_string(i)});
    }

    muxNTest->setDef(def);

    c->runPasses(
      {"rungenerators", "flatten", "flattentypes", "wireclocks-clk"});

    SimulatorState state(muxNTest);
    for (uint i = 0; i < N; i++) {
      state.setValue("self.in_data_" + to_string(i), BitVector(width, i));
    }

    state.setValue("self.in_sel", BitVector(7, "0010010"));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVector(16, 18));

    // NGraph gr;
    // buildOrderedGraph(muxNTest, gr);
    // deque<vdisc> topoOrder = topologicalSort(gr);

    // SECTION("Compile and run") {
    //   int s = compileCode(topoOrder, gr, muxNTest, "./gencode/", "mux" +
    //   to_string(N));

    //   REQUIRE(s == 0);
    // }
  }

  SECTION("andr") {
    uint n = 11;

    Generator* andr = c->getGenerator("coreir.andr");
    Type* andrNType = c->Record(
      {{"in", c->Array(n, c->BitIn())}, {"out", c->Bit()}});

    Module* andrN = g->newModuleDecl("andrN", andrNType);
    ModuleDef* def = andrN->newModuleDef();

    Wireable* self = def->sel("self");
    Wireable* andr0 = def->addInstance(
      "andr0",
      andr,
      {{"width", Const::make(c, n)}});

    def->connect(self->sel("in"), andr0->sel("in"));
    def->connect(andr0->sel("out"), self->sel("out"));

    andrN->setDef(def);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});
    // RunGenerators rg;
    // rg.runOnNamespace(g);

    SimulatorState state(andrN);

    SECTION("Bitvector that is all ones") {
      state.setValue("self.in", BitVec(n, "11111111111"));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(1, 1));
    }

    SECTION("Bitvector that is not all ones") {
      state.setValue("self.in", BitVec(n, "11011101111"));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(1, 0));
    }
  }

  SECTION("And 4") {
    cout << "32 bit and 4" << endl;

    uint n = 32;

    Generator* and2 = c->getGenerator("coreir.and");

    // Define And4 Module
    Type* and4Type = c->Record({{"in0", c->Array(n, c->BitIn())},
                                {"in1", c->Array(n, c->BitIn())},
                                {"in2", c->Array(n, c->BitIn())},
                                {"in3", c->Array(n, c->BitIn())},
                                {"out", c->Array(n, c->Bit())}});

    Module* and4_n = g->newModuleDecl("And4", and4Type);
    ModuleDef* def = and4_n->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* and_00 = def->addInstance(
      "and00",
      and2,
      {{"width", Const::make(c, n)}});
    Wireable* and_01 = def->addInstance(
      "and01",
      and2,
      {{"width", Const::make(c, n)}});
    Wireable* and_1 = def->addInstance(
      "and1",
      and2,
      {{"width", Const::make(c, n)}});

    def->connect(self->sel("in0"), and_00->sel("in0"));
    def->connect(self->sel("in1"), and_00->sel("in1"));
    def->connect(self->sel("in2"), and_01->sel("in0"));
    def->connect(self->sel("in3"), and_01->sel("in1"));

    def->connect(and_00->sel("out"), and_1->sel("in0"));
    def->connect(and_01->sel("out"), and_1->sel("in1"));

    def->connect(and_1->sel("out"), self->sel("out"));
    and4_n->setDef(def);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});
    // RunGenerators rg;
    // rg.runOnNamespace(g);

    // How to initialize and track values in the interpreter?
    // I think the right way would be to set select values, but
    // that does not deal with registers and memory that need
    // intermediate values
    SimulatorState state(and4_n);
    state.setValue(self->sel("in0"), BitVec(n, 20));
    state.setValue(self->sel("in1"), BitVec(n, 0));
    state.setValue(self->sel("in2"), BitVec(n, 9));
    state.setValue(self->sel("in3"), BitVec(n, 31));

    state.execute();

    BitVec bv(n, 20 & 0 & 9 & 31);

    cout << "BV     = " << bv << endl;
    cout << "output = " << state.getBitVec(self->sel("out")) << endl;

    REQUIRE(state.getBitVec(self->sel("out")) == bv);
  }

  SECTION("Or 4") {
    cout << "23 bit or 4" << endl;

    uint n = 23;

    Generator* or2 = c->getGenerator("coreir.or");

    // Define Or4 Module
    Type* or4Type = c->Record({{"in0", c->Array(n, c->BitIn())},
                               {"in1", c->Array(n, c->BitIn())},
                               {"in2", c->Array(n, c->BitIn())},
                               {"in3", c->Array(n, c->BitIn())},
                               {"outval", c->Array(n, c->Bit())}});

    Module* or4_n = g->newModuleDecl("Or4", or4Type);
    ModuleDef* def = or4_n->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* or_00 = def->addInstance(
      "or00",
      or2,
      {{"width", Const::make(c, n)}});
    Wireable* or_01 = def->addInstance(
      "or01",
      or2,
      {{"width", Const::make(c, n)}});
    Wireable* or_1 = def->addInstance(
      "or1",
      or2,
      {{"width", Const::make(c, n)}});

    def->connect(self->sel("in0"), or_00->sel("in0"));
    def->connect(self->sel("in1"), or_00->sel("in1"));
    def->connect(self->sel("in2"), or_01->sel("in0"));
    def->connect(self->sel("in3"), or_01->sel("in1"));

    def->connect(or_00->sel("out"), or_1->sel("in0"));
    def->connect(or_01->sel("out"), or_1->sel("in1"));

    def->connect(or_1->sel("out"), self->sel("outval"));
    or4_n->setDef(def);

    c->runPasses({"rungenerators", "flattentypes"});  //,"flatten"});

    // RunGenerators rg;
    // rg.runOnNamespace(g);

    // How to initialize or track values in the interpreter?
    // I think the right way would be to set select values, but
    // that does not deal with registers or memory that need
    // intermediate values
    SimulatorState state(or4_n);

    state.setValue("self.in0", BitVec(n, 20));
    state.setValue(self->sel("in1"), BitVec(n, 0));
    state.setValue(self->sel("in2"), BitVec(n, 9));
    state.setValue(self->sel("in3"), BitVec(n, 31));

    state.execute();

    BitVec bv(n, 20 | 0 | 9 | 31);

    cout << "BV     = " << bv << endl;
    cout << "output = " << state.getBitVec(self->sel("outval")) << endl;

    REQUIRE(state.getBitVec(self->sel("outval")) == bv);
  }

  SECTION("Counter") {
    c->enSymtable();

    addCounter(c, g);

    uint pcWidth = 17;
    Type* counterTestType = c->Record(
      {{"en", c->BitIn()},
       {"clk", c->Named("coreir.clkIn")},
       {"counterOut", c->Array(pcWidth, c->Bit())}});

    Module* counterTest = g->newModuleDecl("counterMod", counterTestType);
    ModuleDef* def = counterTest->newModuleDef();

    def->addInstance(
      "counter",
      "global.myCounter",
      {{"width", Const::make(c, pcWidth)}});

    def->connect("self.en", "counter.en");
    def->connect("self.clk", "counter.clk");
    def->connect("counter.out", "self.counterOut");

    counterTest->setDef(def);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    bool hasSymtab = counterTest->getMetaData().get<map<string, json>>().count(
      "symtable");

    cout << "hasSymtab = " << hasSymtab << endl;

    map<string, json> symdata = counterTest->getMetaData()["symtable"]
                                  .get<map<string, json>>();

    cout << "symdata size = " << symdata.size() << endl;

    for (auto& symEnt : symdata) {
      SelectPath curpath = symdata[symEnt.first].get<SelectPath>();
      cout << symEnt.first << " --> ";
      for (auto& p : curpath) { cout << p << "."; }

      cout << endl;
    }

    // cout << "ct is generator ? " << ct->getModuleRef()->isGenerated() <<
    // endl;

    SimulatorState state(counterTest);

    NGraph& g = state.getCircuitGraph();

    cout << "COUNTER NODES" << endl;
    for (auto& vd : g.getVerts()) {
      cout << g.getNode(vd).getWire()->toString() << endl;
    }
    cout << "DONE NODES." << endl;

    SECTION("Test register defaults") {
      REQUIRE(state.getBitVec("counter$ri$reg0.out") == BitVec(pcWidth, 0));
    }

    SECTION("Test setting and getting registers") {
      state.setRegister("counter$ri$reg0", BitVec(pcWidth, 231));

      auto states = state.getCircStates();

      cout << "# of states = " << states.size() << endl;

      cout << "Register values" << endl;
      for (auto& regVal : states.back().registers) {
        cout << regVal.first << " = " << regVal.second << endl;
      }
      cout << "reg done." << endl;

      REQUIRE(state.getRegister("counter$ri$reg0") == BitVec(pcWidth, 231));
    }

    SECTION("Count from zero, enable set") {

      state.setRegister("counter$ri$reg0", BitVec(pcWidth, 0));
      state.setValue("self.en", BitVec(1, 1));
      state.resetCircuit();

      // state.setClock("self.clk", 0, 1);
      // state.execute();

      SECTION("Before first clock cycle the output is zero") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 0));
      }

      state.setClock("self.clk", 0, 1);
      state.execute();

      SECTION("After first rising clock edge the output is 1") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 1));
      }

      state.execute();

      SECTION("After the second rising clock edge the output is 2") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 2));
      }

      state.setClock("self.clk", 1, 0);
      state.execute();

      SECTION("No updates during a falling clock edge") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 2));
      }

      state.setClock("self.clk", 0, 1);
      state.execute();

      SECTION("After the third rising clock edge the output is 3") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 3));
      }
    }

    SECTION("Counting with clock changes, enable set") {

      state.setRegister("counter$ri$reg0", BitVec(pcWidth, 400));
      state.setValue("self.en", BitVec(1, 1));
      state.resetCircuit();
      state.setClock("self.clk", 0, 1);

      // state.execute();

      SECTION("Value is 400 after setting register") {
        REQUIRE(state.getRegister("counter$ri$reg0") == BitVec(pcWidth, 400));
      }

      state.execute();

      cout << "Output = " << state.getBitVec("self.counterOut") << endl;

      SECTION("Value is 401 after first tick") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 401));
      }

      state.setClock("self.clk", 1, 0);

      state.execute();

      SimValue* clkSimVal = state.getValue("self.clk");

      REQUIRE(clkSimVal != nullptr);

      ClockValue* clkVal = toClock(clkSimVal);

      cout << "last clock = " << (int)clkVal->lastValue() << endl;
      cout << "curr clock = " << (int)clkVal->value() << endl;

      cout << "Output = " << state.getBitVec("self.counterOut") << endl;

      SECTION("Value is 401 after second tick") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 401));
      }

      state.setClock("self.clk", 1, 0);

      state.execute();

      SECTION("Value is still 401") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 401));
      }

      state.setClock("self.clk", 0, 1);

      state.execute();

      SECTION("Value is now 402") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 402));
      }
    }

    SECTION("Enable on") {

      state.setRegister("counter$ri$reg0", BitVec(pcWidth, 400));
      state.setValue("self.en", BitVec(1, 1));
      state.setClock("self.clk", 1, 0);

      state.execute();

      cout << "Output = " << state.getBitVec("self.counterOut") << endl;

      REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 400));
    }

    SECTION("Setting watchpoint") {

      state.setRegister("counter$ri$reg0", BitVec(pcWidth, 0));
      state.setClock("self.clk", 1, 0);
      state.setValue("self.en", BitVec(1, 1));

      state.setWatchPoint("self.counterOut", BitVec(pcWidth, 10));

      state.run();

      SECTION("Stop at watchpoint") {
        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 10));
      }

      // Should rewind rewind 1 clock cycle or one half clock?
      SECTION("Rewinding state by 1 clock cycle") {

        cout << "state index before rewind = " << state.getStateIndex() << endl;
        state.rewind(2);
        cout << "state index after rewind  = " << state.getStateIndex() << endl;

        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 9));
      }

      SECTION("Rewinding the changes clock cycle count") {

        ClockValue* clk = toClock(state.getValue("self.clk"));

        int oldCount = clk->getHalfCycleCount();

        state.rewind(3);

        ClockValue* clockAfterRewind = toClock(state.getValue("self.clk"));
        int newCount = clockAfterRewind->getHalfCycleCount();

        REQUIRE(newCount == (oldCount - 3));

        state.runHalfCycle();

        ClockValue* clockLater = toClock(state.getValue("self.clk"));

        int countLater = clockLater->getHalfCycleCount();

        REQUIRE(countLater == (newCount + 1));
      }

      SECTION("Setting a value after rewinding reverts all earlier states") {

        int numStates = state.getCircStates().size();

        state.rewind(2);

        REQUIRE(!state.atLastState());

        state.setValue("self.en", BitVec(1, 0));

        REQUIRE(state.atLastState());

        REQUIRE(state.getCircStates().size() == (numStates - 2));
      }

      SECTION(
        "Rewinding and then running to an already simulated point fast "
        "forwards") {
        state.rewind(4);

        int numStates = state.getCircStates().size();

        state.runHalfCycle();

        REQUIRE(state.getCircStates().size() == numStates);
      }

      SECTION("Rewinding to before the start of the simulation is an error") {

        bool rewind = state.rewind(22);

        REQUIRE(!rewind);
      }

      SECTION("Deleting watchpoint and re-running back to earlier state") {
        state.deleteWatchPoint("self.counterOut");

        state.setWatchPoint("self.counterOut", BitVec(pcWidth, 5));

        state.runBack();

        REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 5));
      }
    }

    SECTION("Finding values using unflattened-names") {

      state.setValue("self.en", BitVector(1, 1));

      SECTION("self.en") {
        SimValue* val = state.getValueByOriginalName({"self"}, {"en"});

        REQUIRE(val->getType() == SIM_VALUE_BV);
      }

      SECTION("counter.en") {
        auto val = state.getValueByOriginalName({"counter"}, {"en"});

        REQUIRE(val->getType() == SIM_VALUE_BV);
      }
    }
  }

  SECTION("Test bit vector addition") {
    cout << "23 bit or 4" << endl;

    uint n = 76;

    Generator* add2 = c->getGenerator("coreir.add");

    // Define Add2 Module
    Type* add2Type = c->Record({{"in0", c->Array(n, c->BitIn())},
                                {"in1", c->Array(n, c->BitIn())},
                                {"outval", c->Array(n, c->Bit())}});

    Module* add2_n = g->newModuleDecl("Add2", add2Type);
    ModuleDef* def = add2_n->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* or_00 = def->addInstance(
      "or00",
      add2,
      {{"width", Const::make(c, n)}});

    def->connect(self->sel("in0"), or_00->sel("in0"));
    def->connect(self->sel("in1"), or_00->sel("in1"));
    def->connect(or_00->sel("out"), self->sel("outval"));

    add2_n->setDef(def);

    // RunGenerators rg;
    // rg.runOnNamespace(g);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    // How to initialize or track values in the interpreter?
    // I think the right way would be to set select values, but
    // that does not deal with registers or memory that need
    // intermediate values
    SimulatorState state(add2_n);
    // state.setValue(self->sel("in0"), BitVec(n, 20));
    state.setValue("self.in0", BitVec(n, 20));
    state.setValue("self.in1", BitVec(n, 1234));

    state.execute();

    BitVec bv(n, 20 + 1234);

    cout << "BV     = " << bv << endl;
    cout << "output = " << state.getBitVec(self->sel("outval")) << endl;

    REQUIRE(state.getBitVec(self->sel("outval")) == bv);
  }

  SECTION("Multiplexer") {
    uint width = 30;

    Type* muxType = c->Record({{"in0", c->Array(width, c->BitIn())},
                               {"in1", c->Array(width, c->BitIn())},
                               {"sel", c->BitIn()},
                               {"out", c->Array(width, c->Bit())}});

    Module* muxTest = g->newModuleDecl("muxTest", muxType);
    ModuleDef* def = muxTest->newModuleDef();

    Wireable* mux = def->addInstance(
      "m0",
      "coreir.mux",
      {{"width", Const::make(c, width)}});

    def->connect("self.in0", "m0.in0");
    def->connect("self.in1", "m0.in1");
    def->connect("self.sel", "m0.sel");
    def->connect("m0.out", "self.out");

    muxTest->setDef(def);

    SECTION("Select input 1") {
      SimulatorState state(muxTest);
      state.setValue("self.in0", BitVec(width, 1234123));
      state.setValue("self.in1", BitVec(width, 987));
      state.setValue("self.sel", BitVec(1, 1));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(width, 987));
    }

    SECTION("Select input 0") {
      SimulatorState state(muxTest);
      state.setValue("self.in0", BitVec(width, 1234123));
      state.setValue("self.in1", BitVec(width, 987));
      state.setValue("self.sel", BitVec(1, 0));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(width, 1234123));
    }
  }

  SECTION("Increment circuit") {
    uint width = 3;

    Type* incTestType = c->Record({{"incIn", c->Array(width, c->BitIn())},
                                   {"incOut", c->Array(width, c->Bit())}});

    Module* incTest = g->newModuleDecl("incMod", incTestType);
    ModuleDef* def = incTest->newModuleDef();

    // assert(false);
    // Value wArg({{"width", Const::make(c,width)}});
    Values wArg({{"width", Const::make(c, width)}});
    def->addInstance("ai", "coreir.add", wArg);
    def->addInstance(
      "ci",
      "coreir.const",
      wArg,
      {{"value", Const::make(c, BitVector(width, 1))}});

    def->connect("ci.out", "ai.in0");
    def->connect("self.incIn", "ai.in1");
    def->connect("ai.out", "self.incOut");

    incTest->setDef(def);

    SimulatorState state(incTest);
    state.setValue("self.incIn", BitVec(width, 0));

    state.execute();

    REQUIRE(state.getBitVec("self.incOut") == BitVec(width, 1));
  }
  SECTION("Memory") {
    uint width = 20;
    uint depth = 4;
    uint index = 2;

    Type* memoryType = c->Record({{"clk", c->Named("coreir.clkIn")},
                                  {"write_data", c->BitIn()->Arr(width)},
                                  {"write_addr", c->BitIn()->Arr(index)},
                                  {"write_en", c->BitIn()},
                                  {"read_data", c->Bit()->Arr(width)},
                                  {"read_addr", c->BitIn()->Arr(index)}});

    Module* memory = c->getGlobal()->newModuleDecl("memory0", memoryType);
    ModuleDef* def = memory->newModuleDef();

    def->addInstance(
      "m0",
      "coreir.mem",
      {{"width", Const::make(c, width)}, {"depth", Const::make(c, depth)}});

    def->connect("self.clk", "m0.clk");
    def->connect("self.write_en", "m0.wen");
    def->connect("self.write_data", "m0.wdata");
    def->connect("self.write_addr", "m0.waddr");
    def->connect("self.read_data", "m0.rdata");
    def->connect("self.read_addr", "m0.raddr");

    memory->setDef(def);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    SimulatorState state(memory);

    state.setClock("self.clk", 0, 1);
    state.setValue("self.write_en", BitVec(1, 0));
    state.setValue("self.write_addr", BitVec(index, 0));
    state.setValue("self.write_data", BitVec(width, 23));
    state.setValue("self.read_addr", BitVec(index, 0));

    state.exeCombinational();
    REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 0));
    state.execute();
    state.setValue("self.write_en", BitVec(1, 1));
    state.exeCombinational();
    REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 0));
    REQUIRE(state.getBitVec("self.write_addr") == BitVec(index, 0));
    state.execute();
    REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 23));
    state.setValue("self.write_addr", BitVec(index, 1));
    state.setValue("self.write_data", BitVec(width, 5));
    state.setValue("self.read_addr", BitVec(index, 1));
    state.exeCombinational();
    REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 0));
    state.execute();
    REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 5));
  }

  SECTION("ROM") {
    uint width = 20;
    uint depth = 4;
    uint index = 2;

    Type* memoryType = c->Record({{"clk", c->Named("coreir.clkIn")},
                                  {"read_data", c->Bit()->Arr(width)},
                                  {"read_addr", c->BitIn()->Arr(index)}});

    Module* memory = c->getGlobal()->newModuleDecl("memory0", memoryType);
    ModuleDef* def = memory->newModuleDef();

    Json vals;
    for (int i = 0; i < (int)depth; i++) {
      // BitVector bv(width, i);
      // vals.emplace_back(bv.hex_string());
      // vals.emplace_back(to_string(i));
      // vals["init"].emplace_back(i);
      vals["init"].emplace_back(i);
    }

    def->addInstance(
      "m0",
      "memory.rom",
      {{"width", Const::make(c, width)}, {"depth", Const::make(c, depth)}},
      {{"init", Const::make(c, vals)}});

    def->addInstance(
      "rdConst",
      "coreir.const",
      {{"width", Const::make(c, 1)}},
      {{"value", Const::make(c, BitVector(1, 1))}});

    def->connect("self.clk", "m0.clk");
    def->connect("self.read_data", "m0.rdata");
    def->connect("self.read_addr", "m0.raddr");
    def->connect("m0.ren", "rdConst.out.0");

    memory->setDef(def);

    if (!saveToFile(g, "rom_unit_test_mod.json", memory)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    if (!saveToFile(g, "rom_unit_test_mod_inlined.json", memory)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }
    cout << "Starting test of ROM" << endl;
    SimulatorState state(memory);

    state.setClock("self.clk", 0, 1);
    state.setValue("self.read_addr", BitVec(index, 1));
    state.exeCombinational();
    state.execute();

    REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 1));

    cout << "Done with ROM" << endl;
  }

  SECTION("ROM2") {

    cout << "Starting ROM2" << endl;

    uint width = 16;
    uint depth = 4;
    uint index = width;

    Type* memoryType = c->Record({{"clk", c->Named("coreir.clkIn")},
                                  {"read_data", c->Bit()->Arr(width)},
                                  {"read_addr", c->BitIn()->Arr(index)}});

    Module* memory = c->getGlobal()->newModuleDecl("memory0", memoryType);
    ModuleDef* def = memory->newModuleDef();

    Json vals;
    for (int i = 0; i < (int)depth; i++) {
      // vals.emplace_back(to_string(i));
      vals["init"].emplace_back(i);
    }

    def->addInstance(
      "m0",
      "memory.rom2",
      {{"width", Const::make(c, width)}, {"depth", Const::make(c, depth)}},
      {{"init", Const::make(c, vals)}});

    def->addInstance(
      "rdConst",
      "coreir.const",
      {{"width", Const::make(c, 1)}},
      {{"value", Const::make(c, BitVector(1, 1))}});

    def->connect("self.clk", "m0.clk");
    def->connect("self.read_data", "m0.rdata");
    def->connect("self.read_addr", "m0.raddr");
    def->connect("m0.ren", "rdConst.out.0");

    memory->setDef(def);

    if (!saveToFile(g, "rom2_unit_test_mod.json", memory)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    if (!saveToFile(g, "rom2_unit_test_mod_after_opt.json", memory)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }

    cout << "After optimization" << endl;
    memory->print();

    cout << "Starting test of ROM" << endl;
    SimulatorState state(memory);

    state.setClock("self.clk", 0, 1);
    state.setValue("self.read_addr", BitVec(index, 1));
    state.exeCombinational();
    state.execute();

    REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 1));
  }

  SECTION("Memory2") {
    uint width = 20;
    uint depth = 4;
    uint index = 2;

    Type* memoryType = c->Record({{"clk", c->Named("coreir.clkIn")},
                                  {"write_data", c->BitIn()->Arr(width)},
                                  {"write_addr", c->BitIn()->Arr(index)},
                                  {"write_en", c->BitIn()},
                                  {"read_data", c->Bit()->Arr(width)},
                                  {"read_addr", c->BitIn()->Arr(index)}});

    Module* memory = c->getGlobal()->newModuleDecl("memory0", memoryType);
    ModuleDef* def = memory->newModuleDef();

    def->addInstance(
      "m0",
      "coreir.mem",
      {{"width", Const::make(c, width)}, {"depth", Const::make(c, depth)}});

    def->connect("self.clk", "m0.clk");
    def->connect("self.write_en", "m0.wen");
    def->connect("self.write_data", "m0.wdata");
    def->connect("self.write_addr", "m0.waddr");
    def->connect("self.read_data", "m0.rdata");
    def->connect("self.read_addr", "m0.raddr");

    memory->setDef(def);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    SimulatorState state(memory);

    SECTION("Memory default is zero") {
      REQUIRE(state.getMemory("m0", BitVec(index, 0)) == BitVec(width, 0));
    }

    SECTION("rdata default is zero") {
      REQUIRE(state.getBitVec("m0.rdata") == BitVec(width, 0));
    }

    state.setMemory("m0", BitVec(index, 0), BitVec(width, 0));
    state.setMemory("m0", BitVec(index, 1), BitVec(width, 1));
    state.setMemory("m0", BitVec(index, 2), BitVec(width, 2));
    state.setMemory("m0", BitVec(index, 3), BitVec(width, 3));

    SECTION("Setting memory manually") {
      REQUIRE(state.getMemory("m0", BitVec(index, 2)) == BitVec(width, 2));
    }

    SECTION("Re-setting memory manually") {
      state.setMemory("m0", BitVec(index, 3), BitVec(width, 23));

      REQUIRE(state.getMemory("m0", BitVec(index, 3)) == BitVec(width, 23));
    }

    SECTION("Write to address zero") {

      SECTION("Read is combinational") {
        state.setClock("self.clk", 0, 0);
        state.setValue("self.write_en", BitVec(1, 0));
        state.setValue("self.write_addr", BitVec(index, 0));
        state.setValue("self.write_data", BitVec(width, 23));

        state.setValue("self.read_addr", BitVec(index, 2));

        state.execute();

        REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 2));

        state.setClock("self.clk", 0, 0);
        state.setValue("self.read_addr", BitVec(index, 0));

        state.execute();

        REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 0));
      }

      state.setClock("self.clk", 0, 1);
      state.setValue("self.write_en", BitVec(1, 1));
      state.setValue("self.write_addr", BitVec(index, 0));
      state.setValue("self.write_data", BitVec(width, 23));
      state.setValue("self.read_addr", BitVec(index, 0));

      state.exeCombinational();

      SECTION(
        "read_data is 0 after zeroth clock cycle, even though the address "
        "being read is set by write_addr") {
        REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 0));
      }

      state.execute();

      SECTION("read_data is 23 after the first rising edge") {
        REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 23));
      }

      state.execute();

      SECTION(
        "One cycle after setting write_data the result has been updated") {
        REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 23));
      }

      state.execute();

      cout << "read data later = " << state.getBitVec("self.read_data") << endl;

      SECTION("Re-updating does not change the value") {
        REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 23));
      }
    }
  }

  /*
      SECTION("Rowbuffer") {

        uint index = 4;
        uint width = index;
        uint depth = 10;

        CoreIRLoadLibrary_commonlib(c);

        Type* lineBufferMemType = c->Record({
          {"clk", c->Named("coreir.clkIn")},
          {"wdata", c->BitIn()->Arr(width)},
          {"rdata", c->Bit()->Arr(width)},
          {"wen", c->BitIn()},
          {"valid", c->Bit()},
          {"flush", c->BitIn()}
        });

        Module* lbMem = c->getGlobal()->newModuleDecl("lbMem",
     lineBufferMemType); ModuleDef* def = lbMem->newModuleDef();

        def->addInstance("m0",
                         "memory.rowbuffer",
                         {{"width", Const::make(c, width)},
                             {"depth", Const::make(c, depth)}});

        def->connect("self.clk", "m0.clk");
        def->connect("self.wen", "m0.wen");
        def->connect("self.wdata", "m0.wdata");
        def->connect("m0.rdata", "self.rdata");
        def->connect("m0.valid", "self.valid");
        def->connect("self.flush", "m0.flush");

        lbMem->setDef(def);

        if (!saveToFile(g, "no_flat_linebuffermem_off_2.json",lbMem)) {
          cout << "Could not save to json!!" << endl;
          c->die();
        }

        c->runPasses({"rungenerators","verifyconnectivity","flattentypes",
     "flatten","verifyconnectivity"});

        if (!saveToFile(g, "linebuffermem.json",lbMem)) {
          cout << "Could not save to json!!" << endl;
          c->die();
        }

        SimulatorState state(lbMem);

        state.setValue("self.wdata", BitVector(width, "0"));
        state.setValue("self.wen", BitVector(1, "0"));
        state.setValue("self.flush", BitVector(1, "0"));
        state.resetCircuit();

        state.setClock("self.clk", 0, 1);

        BitVector one(width, "1");
        BitVector val(width, "1");

        cout << "ROWBUFFER BEHAVIOR" << endl;
        //Loading up the rowbuffer
        for (uint i = 0; i < depth; i++) {
          state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1, "1"));
          cout << "after setting value " << toString(val) << endl;
          state.exeCombinational();
          //cout << "raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "self.rdata " << (i) << " = " <<
     state.getBitVec("self.rdata") << endl;
          //cout << "self.valid " << (i) << " = " <<
     state.getBitVec("self.valid") << endl;
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, "0"));
          state.execute();
          val = add_general_width_bv(val, one);
        }
        //Loading and reading (steady state)
        for (uint i = 0; i < depth; i++) {
          cout << "LR self.rdata " << (i) << " = " <<
     state.getBitVec("self.rdata") << endl; cout << "LR self.valid " << (i) << "
     = " << state.getBitVec("self.valid") << endl;
          //cout << "LR raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "LR waddr " << (i) << " = " <<
     state.getBitVec("m0$waddr$r$reg0.out") << endl;
                //cout << "mem[0] " << (i) << " = " << state.getMemory("m0$mem",
     BitVec(4, 0)) << endl;
                //cout << "mem[1] " << (i) << " = " << state.getMemory("m0$mem",
     BitVec(4, 1)) << endl;
                //cout << "mem.addr " << (i) << " = " <<
     state.getBitVec("m0$mem.raddr") << endl;
          //state.exeCombinational(); //TODO It works if This is here, but fails
     if it is missing REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1,1));
          cout << "setting wdata to " << val << endl;
          state.exeCombinational();
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          //cout << "LR2 raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "LR2 waddr " << (i) << " = " <<
     state.getBitVec("m0$waddr$r$reg0.out") << endl; state.execute(); val =
     add_general_width_bv(val, one);
        }

        //Loading and reading (steady state)
        for (uint i = depth; i < 2*depth; i++) {
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1,1));
          cout << "setting wdata to " << val << endl;
          state.exeCombinational();
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          //cout << "LR2 raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "LR2 waddr " << (i) << " = " <<
     state.getBitVec("m0$waddr$r$reg0.out") << endl; state.execute(); val =
     add_general_width_bv(val, one);
        }

        state.setValue("self.wdata", val);
        state.setValue("self.wen", BitVector(1,0));
        state.exeCombinational();
        REQUIRE(state.getBitVec("self.valid") == BitVec(1, 0));
        state.execute();
        state.setValue("self.wen", BitVector(1,1));
        state.exeCombinational();

        //just reading
        for (uint i = 0; i < depth; i++) {
          cout << "R" << i << " self.rdata " << (i) << " = " <<
     state.getBitVec("self.rdata") << endl; cout << "R" << i << " self.valid "
     << (i) << " = " << state.getBitVec("self.valid") << endl;
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, "1"));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width,
     (2*depth+i+1)%16)); state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1,1));
          state.execute();
          val = add_general_width_bv(val, one);
        }

      }
  */
  /*
      SECTION("Rowbuffer power of 2") {

        uint index = 4;
        uint width = index;
        uint depth = 16;

        CoreIRLoadLibrary_commonlib(c);

        Type* lineBufferMemType = c->Record({
          {"clk", c->Named("coreir.clkIn")},
          {"wdata", c->BitIn()->Arr(width)},
          {"rdata", c->Bit()->Arr(width)},
          {"wen", c->BitIn()},
          {"valid", c->Bit()},
          {"flush", c->BitIn()}
        });

        Module* lbMem = c->getGlobal()->newModuleDecl("lbMem",
     lineBufferMemType); ModuleDef* def = lbMem->newModuleDef();

        def->addInstance("m0",
                         "memory.rowbuffer",
                         {{"width", Const::make(c, width)},
                             {"depth", Const::make(c, depth)}});

        def->connect("self.clk", "m0.clk");
        def->connect("self.wen", "m0.wen");
        def->connect("self.wdata", "m0.wdata");
        def->connect("m0.rdata", "self.rdata");
        def->connect("m0.valid", "self.valid");
        def->connect("self.flush", "m0.flush");

        lbMem->setDef(def);

        if (!saveToFile(g, "no_flat_linebuffermem_off_2.json",lbMem)) {
          cout << "Could not save to json!!" << endl;
          c->die();
        }

        c->runPasses({"rungenerators","verifyconnectivity","flattentypes",
     "flatten","verifyconnectivity"});

        if (!saveToFile(g, "linebuffermem.json",lbMem)) {
          cout << "Could not save to json!!" << endl;
          c->die();
        }

        SimulatorState state(lbMem);

        state.setValue("self.wdata", BitVector(width, "0"));
        state.setValue("self.wen", BitVector(1, "0"));
        state.setValue("self.flush", BitVector(1, "0"));
        state.resetCircuit();

        state.setClock("self.clk", 0, 1);

        BitVector one(width, "1");
        BitVector val(width, "1");

        cout << "ROWBUFFER BEHAVIOR" << endl;
        //Loading up the rowbuffer
        for (uint i = 0; i < depth; i++) {
          state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1, "1"));
          cout << "after setting value " << toString(val) << endl;
          state.exeCombinational();
          //cout << "raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "self.rdata " << (i) << " = " <<
     state.getBitVec("self.rdata") << endl;
          //cout << "self.valid " << (i) << " = " <<
     state.getBitVec("self.valid") << endl;
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, "0"));
          state.execute();
          val = add_general_width_bv(val, one);
        }
        //Loading and reading (steady state)
        for (uint i = 0; i < depth; i++) {
          cout << "LR self.rdata " << (i) << " = " <<
     state.getBitVec("self.rdata") << endl; cout << "LR self.valid " << (i) << "
     = " << state.getBitVec("self.valid") << endl;
          //cout << "LR raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "LR waddr " << (i) << " = " <<
     state.getBitVec("m0$waddr$r$reg0.out") << endl;
                //cout << "mem[0] " << (i) << " = " << state.getMemory("m0$mem",
     BitVec(4, 0)) << endl;
                //cout << "mem[1] " << (i) << " = " << state.getMemory("m0$mem",
     BitVec(4, 1)) << endl;
                //cout << "mem.addr " << (i) << " = " <<
     state.getBitVec("m0$mem.raddr") << endl;
          //state.exeCombinational(); //TODO It works if This is here, but fails
     if it is missing REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1,1));
          cout << "setting wdata to " << val << endl;
          state.exeCombinational();
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          //cout << "LR2 raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "LR2 waddr " << (i) << " = " <<
     state.getBitVec("m0$waddr$r$reg0.out") << endl; state.execute(); val =
     add_general_width_bv(val, one);
        }

        //Loading and reading (steady state)
        for (uint i = depth; i < 2*depth; i++) {
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1,1));
          cout << "setting wdata to " << val << endl;
          state.exeCombinational();
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width, i+1));
          //cout << "LR2 raddr " << (i) << " = " <<
     state.getBitVec("m0$raddr$r$reg0.out") << endl;
          //cout << "LR2 waddr " << (i) << " = " <<
     state.getBitVec("m0$waddr$r$reg0.out") << endl; state.execute(); val =
     add_general_width_bv(val, one);
        }

        state.setValue("self.wdata", val);
        state.setValue("self.wen", BitVector(1,0));
        state.exeCombinational();
        REQUIRE(state.getBitVec("self.valid") == BitVec(1, 0));
        state.execute();
        state.setValue("self.wen", BitVector(1,1));
        state.exeCombinational();

        //just reading
        for (uint i = 0; i < depth; i++) {
          cout << "R" << i << " self.rdata " << (i) << " = " <<
     state.getBitVec("self.rdata") << endl; cout << "R" << i << " self.valid "
     << (i) << " = " << state.getBitVec("self.valid") << endl;
          REQUIRE(state.getBitVec("self.valid") == BitVec(1, "1"));
          REQUIRE(state.getBitVec("self.rdata") == BitVec(width,
     (2*depth+i+1)%16)); state.setValue("self.wdata", val);
          state.setValue("self.wen", BitVector(1,1));
          state.execute();
          val = add_general_width_bv(val, one);
        }

      }
  */
  SECTION("Slice") {
    uint inLen = 7;
    uint lo = 2;
    uint hi = 5;
    uint outLen = hi - lo;

    Type* sliceType = c->Record({{"in", c->Array(inLen, c->BitIn())},
                                 {"out", c->Array(outLen, c->Bit())}});

    Module* sliceM = c->getGlobal()->newModuleDecl("sliceM", sliceType);
    ModuleDef* def = sliceM->newModuleDef();

    def->addInstance(
      "sl",
      "coreir.slice",
      {{"width", Const::make(c, inLen)},
       {"lo", Const::make(c, lo)},
       {"hi", Const::make(c, hi)}});

    def->connect("self.in", "sl.in");
    def->connect("sl.out", "self.out");

    sliceM->setDef(def);

    SimulatorState state(sliceM);
    state.setValue("self.in", BitVec(inLen, "1011010"));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVec(outLen, "110"));
  }

  SECTION("Concat") {
    uint inLen0 = 3;
    uint inLen1 = 5;
    uint outLen = inLen0 + inLen1;

    Type* concatType = c->Record({{"in0", c->BitIn()->Arr(inLen0)},
                                  {"in1", c->BitIn()->Arr(inLen1)},
                                  {"out", c->Bit()->Arr(outLen)}});

    Module* concatM = c->getGlobal()->newModuleDecl("concatM", concatType);
    ModuleDef* def = concatM->newModuleDef();

    def->addInstance(
      "cm",
      "coreir.concat",
      {{"width0", Const::make(c, inLen0)}, {"width1", Const::make(c, inLen1)}});

    def->connect("self.in0", "cm.in0");
    def->connect("self.in1", "cm.in1");
    def->connect("cm.out", "self.out");

    concatM->setDef(def);

    SimulatorState state(concatM);
    state.setValue("self.in0", BitVec(3, "111"));
    state.setValue("self.in1", BitVec(5, "00000"));

    state.execute();

    REQUIRE(state.getBitVec("self.out") == BitVec(8, "00000111"));
  }

  SECTION("Lookup table") {
    uint n = 4;

    CoreIRLoadLibrary_commonlib(c);

    Generator* lutN = c->getGenerator("commonlib.lutN");
    Type* lutNType = c->Record(
      {{"in", c->Array(n, c->BitIn())}, {"out", c->Bit()}});

    Module* lut4 = g->newModuleDecl("lut4", lutNType);
    ModuleDef* def = lut4->newModuleDef();

    Wireable* self = def->sel("self");
    Wireable* lut0 = def->addInstance(
      "lut0",
      lutN,
      {{"N", Const::make(c, n)}},
      {{"init", Const::make(c, BitVector(1 << n, "1010010111010010"))}});

    def->connect(self->sel("in"), lut0->sel("in"));
    def->connect(lut0->sel("out"), self->sel("out"));

    lut4->setDef(def);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    SimulatorState state(lut4);

    SECTION("lut(6) == 1") {
      state.setValue("self.in", BitVector(n, "0110"));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(1, 1));
    }

    SECTION("lut(0) == 0") {
      state.setValue("self.in", BitVector(n, "0000"));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(1, 0));
    }
  }

  SECTION("D flip flop") {
    Namespace* common = CoreIRLoadLibrary_commonlib(c);

    Module* dff = c->getModule("corebit.reg");
    Type* dffType = c->Record({{"IN", c->BitIn()},
                               {"CLK", c->Named("coreir.clkIn")},
                               {"OUT", c->Bit()}});

    Module* dffTest = g->newModuleDecl("dffTest", dffType);
    ModuleDef* def = dffTest->newModuleDef();

    Wireable* dff0 = def->addInstance(
      "dff0",
      dff,
      {{"init", Const::make(c, true)}});

    Wireable* self = def->sel("self");
    def->connect("self.IN", "dff0.in");
    def->connect("self.CLK", "dff0.clk");
    def->connect("dff0.out", "self.OUT");

    dffTest->setDef(def);

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    // map<string,json> symdata =
    //   dff->getMetaData()["symtable"].get<map<string,json>>();

    // for (auto& symEnt : symdata) {
    //   SelectPath curpath = symdata[symEnt.first].get<SelectPath>();
    //   for (auto& p : curpath) {
    //     cout << p << "$";
    //   }

    //   cout << endl;
    // }

    SimulatorState state(dffTest);
    state.setClock("self.CLK", 0, 1);
    state.setValue("self.IN", BitVec(1, 1));

    state.execute();

    SECTION("After first execute value is 1") {
      REQUIRE(state.getBitVec("self.OUT") == BitVec(1, 1));
    }

    state.setValue("self.IN", BitVec(1, 0));

    state.execute();

    SECTION("After second execute value is 0") {
      REQUIRE(state.getBitVec("self.OUT") == BitVec(1, 0));
    }
  }

  SECTION("Selecting bits from a bit vector") {
    Namespace* common = CoreIRLoadLibrary_commonlib(c);

    cout << "loading" << endl;
    // if (!loadFromFile(c,"./sim_ready_sorter.json")) {
    if (!loadFromFile(c, "./sorter.json")) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }

    c->runPasses({"rungenerators", "flattentypes", "flatten"});

    Module* m = g->getModule("Sorter8");

    assert(m != nullptr);

    SimulatorState state(m);
    state.setValue("self.I", BitVector(8, "10010011"));

    cout << "# of nodes in circuit = "
         << state.getCircuitGraph().getVerts().size() << endl;

    BitVector one(16, "1");
    BitVector nextIn(16, "0");

    std::clock_t start, end;

    start = std::clock();

    state.execute();

    end = std::clock();

    std::cout << "Done. Time to simulate = "
              << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
              << std::endl;

    cout << "out = " << state.getBitVec("self.O") << endl;

    REQUIRE(state.getBitVec("self.O") == BitVector(8, "11110000"));
  }

  /*
  SECTION("conv_3_1 from json") {

    Namespace* common = CoreIRLoadLibrary_commonlib(c);

    cout << "loading" << endl;

    if (!loadFromFile(c,"./conv_3_1.json")) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }

    c->runPasses({"rungenerators", "flattentypes", "flatten",
  "wireclocks-clk"});

    Module* m = g->getModule("DesignTop");

    assert(m != nullptr);

    SimulatorState state(m);
    state.setValue("self.in_0", BitVector(16, "0000000000000001"));
    state.setClock("self.clk", 0, 1);

    BitVector one(16, "1");
    BitVector zero(16, "0");
    BitVector inVal = one; //zero;

    int val = 1;

    int lastClk = 0;
    int nextClk = 1;

    state.setClock("self.clk", lastClk, nextClk);
    state.setValue("self.in_0", BitVec(16, val));

    for (int i = 0; i < 41; i++) {
      nextClk = i % 2;

      state.setClock("self.clk", lastClk, nextClk);

      state.execute();

      if ((i % 2) == 0) {
        cout << "Output " << i << " = " <<
          state.getBitVec("self.out").to_type<uint16_t>() << endl;
      }

      if ((i % 2) == 1) {
        val = val + 1;

        state.setValue("self.in_0", BitVec(16, val));
      }

      lastClk = nextClk;

    }

    REQUIRE(state.getBitVec("self.out") == BitVec(16, 205));

  }
  */

  SECTION("Failing clock test") {

    cout << "loading" << endl;
    if (!loadFromFile(c, "./simple_register_example.json")) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }

    Module* regMod = g->getModule("simple_flattened");
    SimulatorState state(regMod);

    SECTION("2 unset inputs") { REQUIRE(state.unsetInputs().size() == 2); }

    state.execute();

    state.setClock("self.CLK", 0, 1);

    SECTION("1 unset inputs") { REQUIRE(state.unsetInputs().size() == 1); }

    state.setValue("self.I0", BitVec(2, "11"));

    SECTION("0 unset inputs") { REQUIRE(state.unsetInputs().size() == 0); }

    state.execute();
    state.execute();

    SimValue* val = state.getValue("self.CLK");
    assert(val->getType() == SIM_VALUE_CLK);

    ClockValue* clkVal = static_cast<ClockValue*>(val);

    REQUIRE(state.getBitVec("self.O") == BitVec(2, "11"));
    REQUIRE(clkVal->value() == 1);
    REQUIRE(clkVal->lastValue() == 0);
  }

  SECTION("Counter 2 read by original name") {
    c->enSymtable();

    if (!loadFromFile(c, "./tmprb3ud4p2.json")) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }

    c->runPasses(
      {"rungenerators", "flattentypes", "flatten", "wireclocks-clk"});

    Module* regMod = g->getModule("simple");
    SimulatorState state(regMod);
    state.resetCircuit();

    bool hasSymtab = regMod->getMetaData().get<map<string, json>>().count(
      "symtable");

    cout << "regMod hasSymtab = " << hasSymtab << endl;

    map<string, json> symdata = regMod->getMetaData()["symtable"]
                                  .get<map<string, json>>();

    cout << "symdata size = " << symdata.size() << endl;

    for (auto& symEnt : symdata) {
      SelectPath curpath = symdata[symEnt.first].get<SelectPath>();
      cout << symEnt.first << " --> " << concatSelects(curpath) << endl;
    }

    SECTION("Checking lookup by original names") {
      state.setClock("self.CLK", 0, 1);

      for (uint i = 0; i < 4; i++) {

        state.execute();
        state.stepMainClock();

        cout << "O " << i << " = " << state.getBitVec("self.O") << endl;
      }

      REQUIRE(state.getValueByOriginalName("inst0$inst0.O"));

      for (auto& ent : symdata) {
        SimValue* val = state.getValueByOriginalName(ent.first);

        REQUIRE(val != nullptr);

        if (val->getType() == SIM_VALUE_BV) {
          SimBitVector* valBV = static_cast<SimBitVector*>(val);
          cout << "Value of " << ent.first << " is " << valBV->getBits()
               << endl;
        }
      }
    }

    SECTION("Setting watchpoints by original name") {
      state.setClock("self.CLK", 0, 1);

      state.setWatchPointByOriginalName("inst0.O", BitVector(2, 2));

      state.run();

      SimBitVector* sbv = toSimBitVector(
        state.getValueByOriginalName("inst0.O"));

      cout << "inst0.O = " << sbv->getBits() << endl;

      REQUIRE(sbv->getBits() == BitVector(2, 2));
    }
  }

  SECTION("Yet another magma counter failure") {
    if (!loadFromFile(c, "./tmpvtu16uq5.json")) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }

    c->runPasses(
      {"rungenerators", "flattentypes", "flatten"});  //, "wireclocks-clk"});

    Module* regMod = g->getModule("simple");
    SimulatorState state(regMod);
    state.setClock("self.CLK", 0, 1);
    state.resetCircuit();

    cout << "in yet another magma counter error test" << endl;
    cout << "self.O after reset = " << state.getBitVec("self.O") << endl;

    state.setClock("self.CLK", 0, 1);

    for (uint i = 0; i < 50; i++) {

      state.execute();
      state.stepMainClock();

      cout << "Circuit O " << i << " = " << state.getBitVec("self.O") << endl;
    }
  }

  SECTION("Bit selects in inputs to nodes") {
    if (!loadFromFile(c, "./mantle_counter_flattened.json")) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }

    Module* regMod = g->getModule("simple_flattened");
    SimulatorState state(regMod);
    state.resetCircuit();

    REQUIRE(state.getBitVec("self.O") == BitVec(4, "0000"));

    state.execute();

    state.setClock("self.CLK", 0, 1);

    state.execute();

    REQUIRE(state.getBitVec("self.O") == BitVec(4, "0001"));

    state.execute();

    REQUIRE(state.getBitVec("self.O") == BitVec(4, "0010"));
  }

  // SECTION("Magma fifo example") {

  //  Namespace* common = CoreIRLoadLibrary_commonlib(c);

  //  if (!loadFromFile(c,"./fifo_magma_json.json")) {
  //	cout << "Could not Load from json!!" << endl;
  //	c->die();
  //  }

  //  c->runPasses({"rungenerators", "flattentypes", "flatten",
  //  "wireclocks-clk"});
  //
  //  Module* fifoMod = g->getModule("Fifo");
  //  SimulatorState state(fifoMod);
  //  // state.setValue("self.wdata", BitVector(4, "1010"));
  //  // state.setValue("self.wen", BitVector(4, "1"));
  //  // state.setValue("self.ren", BitVector(4, "0"));
  //  // state.resetCircuit();

  //  // state.setClock("self.CLK", 0, 1);

  //  // state.execute();

  //  // REQUIRE(state.isSet("self.wdata"));
  //}

  deleteContext(c);
}

TEST_CASE("Name generation") {
  vector<string> strs{"counter", "ri", "dummy.out"};

  REQUIRE(concatInlined(strs) == "counter$ri$dummy.out");
}

}  // namespace CoreIR
