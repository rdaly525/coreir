#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"

using namespace CoreIR;

namespace {

TEST(FlattenTypesTests, TestFlattenTypesPreserveNDArray) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/flattentypes_preserve_nd_array.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"flattentypes --ndarray"};
  c->runPasses(passes, {});
  assertPassEq(c, "coreirjson", "golds/flattentypes_preserve_nd_array.json");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
