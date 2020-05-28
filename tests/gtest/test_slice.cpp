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
  assertPassEq<Passes::Verilog>(c, "golds/basic_slice.v");
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
  assertPassEq<Passes::Verilog>(c, "golds/slice_slice.v");
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
  assertPassEq<Passes::Verilog>(c, "golds/select_slice.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
