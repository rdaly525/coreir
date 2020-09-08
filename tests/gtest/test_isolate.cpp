#include <gtest/gtest.h>
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

Module* create_module(Context* c, std::string mname) {
  CoreIRLoadLibrary_commonlib(c);
  auto Bits16 = c->Bit()->Arr(16);
  auto ab = c->Record({
    {"a", c->In(Bits16)},
    {"b", c->In(Bits16)},
  });
  auto g = c->getGlobal();
  auto ports = c->Record({{"in0", ab}, {"in1", ab}, {"out", c->Out(ab)}});
  auto m = g->newModuleDecl(mname, ports);

  // Create a complex definition with mixed primitives, other instances, and
  // complex types
  auto def = m->newModuleDef();

  // Use Constructor view to easily create primitives
  auto C = Constructor(def);

  auto io = def->getInterface();
  auto not_bit = C.not_(def->sel("self.in0.a.0"));
  auto mux4 = def->addInstance(
    "m",
    "commonlib.muxn",
    {
      {"width", Const::make(c, 16)},
      {"N", Const::make(c, 4)},
    });
  def->connect(not_bit, mux4->sel("in")->sel("sel")->sel(0));
  def->connect(not_bit, mux4->sel("in")->sel("sel")->sel(1));
  def->connect("self.in0.a", "m.in.data.0");
  def->connect("self.in0.b", "m.in.data.1");
  def->connect("self.in1.a", "m.in.data.2");

  auto reg = def->addInstance(
    "r0",
    "coreir.reg",
    {{"width", Const::make(c, 16)}});

  // add a primitive op before passing into last data
  auto add_out = C.add(io->sel("in1")->sel("a"), reg->sel("out"));
  def->connect(add_out, mux4->sel("in")->sel("data")->sel(3));

  // connect output of mux to a stream of primitives
  auto mul_out = C.mul(mux4->sel("out"), reg->sel("out"));
  auto sub_out = C.sub(mul_out, mux4->sel("out"));

  // connect back to register input
  def->connect(sub_out, reg->sel("in"));

  // Connect some internal coreir values to the module output
  def->connect(mux4->sel("out"), io->sel("out")->sel("a"));
  def->connect(mul_out, io->sel("out")->sel("b"));
  m->setDef(def);
  return m;
}

TEST(IsolateTest, Test1) {
  auto c = newContext();
  auto m = create_module(c, "m1");
  assert(m->hasDef());
  c->setTop(m);

  // Testing isolate pass
  c->runPasses({"isolate_primitives"});
  c->checkerrors();

  auto def = m->getDef();

  // Module should now contain no primitives
  bool has_primitives = anyOf(def->getInstances(), [](auto it) {
    auto nsname = it.second->getModuleRef()->getNamespace()->getName();
    return nsname == "coreir" || nsname == "corebit";
  });

  ASSERT_TRUE(!has_primitives);

  // Also a single instance with name "___primitives"
  auto isolated_insts = filterOver(def->getInstances(), [](auto it) {
    auto nsname = it.second->getModuleRef()->getName();
    return nsname.find(std::string("___primitives")) != std::string::npos;
  });
  ASSERT_TRUE(isolated_insts.size() == 1);

  auto isolated_inst = isolated_insts.begin()->second;
  auto pmod = isolated_inst->getModuleRef();
  ASSERT_TRUE(pmod->hasDef());

  auto pdef = pmod->getDef();

  // All instances should be primitives
  bool only_primitives = allOf(pdef->getInstances(), [](auto it) {
    auto nsname = it.second->getModuleRef()->getNamespace()->getName();
    return nsname == "coreir" || nsname == "corebit";
  });
  ASSERT_TRUE(only_primitives);

  // Should be 5 primitives
  ASSERT_EQ(pdef->getInstances().size(), 5);

  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
