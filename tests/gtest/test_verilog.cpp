#include "gtest/gtest.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "assert_pass.h"

using namespace CoreIR;

namespace {

TEST(VerilogTests, TestStringModule) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "blackbox_verilog_in.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "blackbox_verilog_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestIntermediateConnection) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "intermediate_connection.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "intermediate_connection_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestArraySelect) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "array_select.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "array_select_golden.v");
  deleteContext(c);
}


TEST(VerilogTests, TestAddInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  Module* top;

  if (!loadFromFile(c, "add.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "add_golden.v");
  deleteContext(c);
}


TEST(VerilogTests, TestTwoInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "two_ops.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "two_ops_golden.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
