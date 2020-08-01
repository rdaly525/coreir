#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(IfReconstructionTests, TestUart) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/uart.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"inline_single_instances",
                                           "rungenerators",
                                           "removebulkconnections",
                                           "flattentypes --ndarray",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/uart.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
