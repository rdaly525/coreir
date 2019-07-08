#include "gtest/gtest.h"
#include "coreir.h"
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

}  // namespace

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
