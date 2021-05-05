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

  if (!loadFromFile(c, "srcs/blackbox_verilog_in.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/blackbox_verilog_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestIntermediateConnection) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/intermediate_connection.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/intermediate_connection_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestArraySelect) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/array_select.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/array_select_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestAddInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  Module* top;

  if (!loadFromFile(c, "srcs/add.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/add_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestTwoInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "srcs/two_ops.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/two_ops_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestDisableWidthCast) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "srcs/two_ops.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline --disable-width-cast"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/two_ops_golden_no_cast.v");
  deleteContext(c);
}

TEST(VerilogTests, TestTwoBitInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "srcs/two_ops_bit.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/two_ops_bit_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestPortOrder) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "srcs/port_order.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/port_order_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestMuxInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/mux.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mux_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestInlineVerilogMetadata) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "srcs/inline_verilog.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/inline_verilog_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestDebugInfo) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/debug_info.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/debug_info_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestVerilatorDebugInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/verilator_debug_inline.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline --verilator_debug"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/verilator_debug_inline_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestRegisterMode) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/register_mode.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/register_mode_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestInlineVerilogTop) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/inline_verilog_top.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/inline_verilog_top_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestUndriven) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "srcs/undriven.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/undriven_golden.v");
  deleteContext(c);
}

TEST(VerilogTests, TestWrappedVerilogTop) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/wrapped_verilog_top.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/wrapped_verilog_top_golden.v");
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
    "verilog --inline --prefix foo_"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/compile_guard.v");
  deleteContext(c);
}

TEST(VerilogTests, TestVerilogBody) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/verilog_body.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline --prefix foo_"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/verilog_body.v");
  deleteContext(c);
}

TEST(VerilogTests, TestVerilogBind) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/bind_uniq_test.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline --prefix bar_ --prefix-extern"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/bind_uniq_test.v");
  deleteContext(c);
}
}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
