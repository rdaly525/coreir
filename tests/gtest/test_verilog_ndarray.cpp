#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"

using namespace CoreIR;

namespace {

TEST(VerilogNDArrayTests, TestVerilogNDArray) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/verilog_nd_array_basic.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "flattentypes --ndarray",
    "verilog --ndarray"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/verilog_nd_array_basic.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
