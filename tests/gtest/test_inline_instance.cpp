#include "gtest/gtest.h"
#include "coreir.h"
#include "coreir/common/logging_lite.hpp"
#include "coreir/ir/coreir_symbol_table.hpp"
#include "coreir/ir/symbol_table_interface.hpp"
#include "coreir/passes/analysis/coreirjson.h"

namespace CoreIR {
namespace {

class InlineInstance : public ::testing::Test {
 public:
  InlineInstance() = default;

  void SetUp() override {
    ctx = newContext();
    if (!loadFromFile(ctx, "srcs/simple_hierarchy.json", &top)) ctx->die();
    assert(top != nullptr);
    ctx->setTop(top->getRefName());
  }

  void TearDown() override {
    deleteContext(ctx);
  }

 protected:
  Context* ctx = nullptr;
  Module* top = nullptr;
};

template <typename VariantType, typename T> void VariantExpectEq(
    const VariantType& container, const T& expected) {
  try {
    auto typed = std::get<T>(container);
    EXPECT_EQ(typed, expected);
  } catch (const std::bad_variant_access&) {
    EXPECT_TRUE(false) << "VariantExpectEq failed with wrong type";
  }
}

TEST_F(InlineInstance, Basic) {
  // Grab handles to Top.baz, Top.baz.bar.
  const auto inst_Top_baz = top->getDef()->getInstances().at("baz");
  const auto inst_Top_baz_bar = inst_Top_baz->getModuleRef()->
      getDef()->getInstances().at("bar");

  // Inline Top.baz.
  inlineInstance(inst_Top_baz);

  // Check that top has an instance of Foo (foo) and Bar (baz$bar).
  EXPECT_EQ(top->getDef()->getInstances().size(), 2);
  for (auto [name, inst] : top->getDef()->getInstances()) {
    if (name == "foo") {
      EXPECT_EQ(inst->getModuleRef()->getName(), "Foo");
    }
    else if(name == "baz$bar") {
      EXPECT_EQ(inst->getModuleRef(), inst_Top_baz_bar->getModuleRef());
    } else {
      EXPECT_TRUE(false) << "Unexpected instance";
    }
  }
}

TEST_F(InlineInstance, SymbolTable) {
  // Grab handles to Top.baz.
  const auto inst_Top_baz = top->getDef()->getInstances().at("baz");

  // Inline Top.baz.
  inlineInstance(inst_Top_baz);

  std::string flattentypes_str = "flattentypes";
  ctx->runPasses({"flattentypes", "verilog"}, {});

  auto table = ctx->getPassManager()->getSymbolTable();
  // Check module names (sanity check).
  EXPECT_EQ(table->getModuleName("Top"), "Top");
  EXPECT_EQ(table->getModuleName("Foo"), "Foo");
  EXPECT_EQ(table->getModuleName("Bar"), "Bar");
  // Check non-inlined instance names.
  VariantExpectEq(table->getInstanceName("Bar", "x"), std::string("x"));
  VariantExpectEq(table->getInstanceName("Foo", "bar"), std::string("bar"));
  VariantExpectEq(table->getInstanceName("Top", "foo"), std::string("foo"));
  // Check inlined instance.
  // NOTE(rsetaluri): Not exactly sure why the const_cast needs to appear this
  // away. Ostensibly, the type returned by
  // symbolTableInlinedInstanceSentinel(), and the type inside the variant are
  // both 'SymbolTableSentinel* const', but it seems a const gets lost in the
  // former.
  VariantExpectEq(
      table->getInstanceName("Top", "baz"),
      const_cast<const SymbolTableSentinel*>(
          symbolTableInlinedInstanceSentinel()));
  VariantExpectEq(
      table->getInlinedInstanceName("Top", {"baz", "bar"}),
      std::string("baz$bar"));
}

}  // namespace
}  // namespace coreir

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
