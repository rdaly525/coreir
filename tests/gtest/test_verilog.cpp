#include "gtest/gtest.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"
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

TEST(VerilogTests, TestTwoBitInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "two_ops_bit.json", &top)) {
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
  assertPassEq<Passes::Verilog>(c, "two_ops_bit_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestMuxInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "mux.json", &top)) {
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
  assertPassEq<Passes::Verilog>(c, "mux_golden.v");
  deleteContext(c);
}
    
TEST(VerilogTests, TestInlineVerilogMetadata) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "inline_verilog.json", &top)) {
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
  assertPassEq<Passes::Verilog>(c, "inline_verilog_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestDebugInfo) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "debug_info.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "debug_info_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestRegisterMode) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "register_mode.json", &top)) {
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
  assertPassEq<Passes::Verilog>(c, "register_mode_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestUndriven) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "undriven.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "undriven_golden.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
