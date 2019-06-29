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
  std::ifstream t("generated_file.txt");
  std::string genfile((std::istreambuf_iterator<char>(t)),
                       std::istreambuf_iterator<char>());
  
  deleteContext(c);
}

}  // namespace

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
