#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(SliceTests, TestBasicSlice) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/basic_slice.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"rungenerators",
                                           "removebulkconnections",
                                           "flattentypes",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/basic_slice.v");
  deleteContext(c);
}

TEST(SliceTests, TestSliceOfSlice) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/slice_slice.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"rungenerators",
                                           "removebulkconnections",
                                           "flattentypes",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/slice_slice.v");
  deleteContext(c);
}

TEST(SliceTests, TestSelectOfSlice) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/select_slice.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"rungenerators",
                                           "removebulkconnections",
                                           "flattentypes",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/select_slice.v");
  deleteContext(c);
}

TEST(SliceTests, TestSliceNestedArrayError) {
  // For now, we don't support slicing non-array of bits
  Context* c = newContext();
  Module* top;

  EXPECT_EXIT(
    loadFromFile(c, "srcs/slice_error.json", &top),
    ::testing::ExitedWithCode(1),
    "ERROR: Slicing of non-array-of-bits is not yet supported, sorry!");
}

TEST(SliceTests, TestCombView) {
  // Verify Wireable.getAllSelects and Wireable.getLocalConnections API still
  // works
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);

  Module* top;

  if (!loadFromFile(c, "srcs/slice_combview.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"rungenerators",
                                           "transform2combview",
                                           "removebulkconnections",
                                           "flattentypes",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/slice_combview.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
