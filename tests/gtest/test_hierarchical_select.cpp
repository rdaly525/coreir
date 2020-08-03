#include <gtest/gtest.h>
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"

using namespace CoreIR;

namespace {

void load_file(Context* context, std::string file_name) {
  Module* top;
  bool result = loadFromFile(context, file_name, &top);
  ASSERT_TRUE(result);
  ASSERT_NE(top, nullptr);
  context->setTop(top->getRefName());
}

void check_verilog(Context* context, std::string gold_file) {
  context->runPasses({"flattentypes", "verilog --inline"}, {});
  assertPassEq(context, "verilog", gold_file);
}

TEST(HierarchicalSelectTest, TestHierarchicalSelectBasic) {
  Context* c = newContext();
  load_file(c, "srcs/hierarchical_select.json");
  check_verilog(c, "golds/hierarchical_select.v");
  deleteContext(c);
}

TEST(HierarchicalSelectTest, TestHierarchicalSelectDouble) {
  Context* c = newContext();
  load_file(c, "srcs/hierarchical_select_2.json");
  check_verilog(c, "golds/hierarchical_select_2.v");
  deleteContext(c);
}

TEST(HierarchicalSelectTest, TestHierarchicalSelectNameAlias) {
  Context* c = newContext();
  load_file(c, "srcs/hierarchical_select_3.json");
  check_verilog(c, "golds/hierarchical_select_3.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
