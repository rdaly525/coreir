#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(VerilogNDArrayTests, TestVerilogNDArray) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/verilog_nd_array_basic.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"flattentypes --ndarray", "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/verilog_nd_array_basic.v");
  deleteContext(c);
}

TEST(VerilogNDArrayTests, TestVerilogNDArrayIndex) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/verilog_nd_array_index.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"flattentypes --ndarray", "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/verilog_nd_array_index.v");
  deleteContext(c);
}

TEST(VerilogNDArrayTests, TestVerilogNDArrayMuxN) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/muxn_ndarray.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "flattentypes --ndarray",
    "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/muxn_ndarray.v");
  deleteContext(c);
}

TEST(VerilogNDArrayTests, TestVerilogNDArrayNestedSize1) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/nested_ndarray_size1.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "flattentypes --ndarray",
    "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/nested_ndarray_size1.v");
  deleteContext(c);
}

TEST(VerilogNDArrayTests, TestVerilogNDArrayDoubleNestedSize1) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/double_nested_ndarray_size1.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "flattentypes --ndarray",
    "verilog"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/double_nested_ndarray_size1.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
