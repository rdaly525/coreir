#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"

using namespace CoreIR;

namespace {

TEST(FlattenTypes2Tests, TestFlattenTypes2Basic) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/flattentypes2_basic.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"flattentypes2"};
  c->runPasses(passes, {});
  assertPassEq(c, "coreirjson", "golds/flattentypes2_basic.json");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
