#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/ir/symbol_table_interface.hpp"

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


TEST(FlattenTypesTests, TestSymbolTable) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/flattentypes_preserve_nd_array.json",  &top)) { c->die();}
  assert(top != nullptr);
  c->setTop(top->getRefName());
  c->setDebug(true);
  SymbolTableInterface* sym = c->getPassManager()->getSymbolTable();
  cout << sym->json() << endl;
  c->runPasses({"flattentypes"});
  assert(c->getPassManager()->getSymbolTable() == sym);
  // Verify the symbol table makes sense.
  // Check I0 (ND-array):
  //     ["I0",["Array",12,["Array",16,["Array",8,"BitIn"]]]]
  for (int i=0; i<12; ++i) {
    for (int j=0; j<16; ++j) {
      auto key = "I0." + std::to_string(i) + "." + std::to_string(j);
      auto val = "I0_" + std::to_string(i) + "_" + std::to_string(j);
      assert(sym->getPortName(top->getName(), key) == val);
    }
  }
  // Check I1 (Record):
  //     ["I1",["Record",[["_0","BitIn"],["_1",["Array",3,"BitIn"]]]]]
  assert(sym->getPortName(top->getName(), "I1._0")== "I1__0");
  assert(sym->getPortName(top->getName(), "I1._1")== "I1__1");

  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
