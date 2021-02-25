#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(VerilogTests, TestStringModule) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "blackbox_verilog_in.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "blackbox_verilog_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestIntermediateConnection) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "intermediate_connection.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "intermediate_connection_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestArraySelect) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "array_select.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "array_select_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestAddInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  Module* top;

  if (!loadFromFile(c, "add.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "add_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestTwoInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "two_ops.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "two_ops_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestDisableWidthCast) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "two_ops.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline --disable-width-cast"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "two_ops_golden_no_cast.v");
  deleteContext(c);
}

TEST(VerilogTests, TestTwoBitInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "two_ops_bit.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "two_ops_bit_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestPortOrder) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "port_order.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "port_order_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestMuxInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "mux.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "mux_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestInlineVerilogMetadata) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "inline_verilog.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "inline_verilog_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestDebugInfo) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "debug_info.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "debug_info_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestVerilatorDebugInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "verilator_debug_inline.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline --verilator_debug"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "verilator_debug_inline_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestRegisterMode) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "register_mode.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "register_mode_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestInlineVerilogTop) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "inline_verilog_top.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "inline_verilog_top_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestUndriven) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "undriven.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "undriven_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestWrappedVerilogTop) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "wrapped_verilog_top.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "wrapped_verilog_top_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestInlineIndex) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/inline_index.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/inline_index.v");
  deleteContext(c);
}

TEST(VerilogTests, TestCompileGuard) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/compile_guard.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/compile_guard.v");
  deleteContext(c);
}
}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
