#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {
TEST(MantleVerilogTests, TestConcatT) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_concat.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_concat.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestSliceT) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_slice.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_slice.v");
  deleteContext(c);
}
}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
