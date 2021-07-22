#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(VerilogMetaData, TestGeneratedModule) {
  Context* c = newContext();

  Namespace* g = c->getGlobal();

  // Declare a TypeGenerator (in global) for addN
  g->newTypeGen(
    "wgen",  // name for the typegen
    {{"width", c->Int()}},
    [](Context* c, Values args) {  // Function to compute type
    Json width = args.at("width")->get<Json>();
    return c->Record(
      {{"in", c->BitIn()->Arr(width)}, {"out", c->Bit()->Arr(width)}});
    }
    );

  g->newGeneratorDecl(
    "addN",
    g->getTypeGen("wgen"),
    {{"width", c->Int()}});

  Module* top = g->newModuleDecl("top", c->Record());
  ModuleDef* def = top->newModuleDef();
  auto inst = def->addInstance("inst", "global.addN", {{"width", Const::make(c, 5)}});
  def->connect(inst->sel("in"), inst->sel("out"));
  top->setDef(def);
  c->setTop(top);

  Module* gen_module = inst->getModuleRef();
  gen_module->getMetaData()["verilog_name"] = "Add5";

  serializeToFile(c, "build/Add5.json");
  assertFileEq("build/Add5.json", "golds/Add5.json");

  const std::vector<std::string> passes = {
    "rungenerators",
    "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/Add5.v");
  deleteContext(c);

}

}