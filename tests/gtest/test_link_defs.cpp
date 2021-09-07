#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(VerilogTests, TestLinkDefs) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  Module* top;

  if (!loadFromFile(c, "srcs/link_def.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/link_def.v");
  deleteContext(c);
}

TEST(VerilogTests, TestLinkDefsDefault) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  Module* top;

  if (!loadFromFile(c, "srcs/link_def_default.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/link_def_default.v");
  deleteContext(c);
}

TEST(VerilogTests, TestLinkDefsNoDefault) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  Module* top;

  if (!loadFromFile(c, "srcs/link_def_no_default.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/link_def_no_default.v");
  deleteContext(c);
}
}
