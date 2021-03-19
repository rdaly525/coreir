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
  // Grab handles to M1.i2, M1.i2.i3.
  const auto inst_M1_i2 = top->getDef()->getInstances().at("i2");

  // Inline M1.i2.
  inlineInstance(inst_M1_i2);

  // Check that M1 has only an instance of M3 named i2$i3.
  EXPECT_EQ(top->getDef()->getInstances().size(), 1);
  for (auto [name, inst] : top->getDef()->getInstances()) {
    if (name == "i2$i3") {
      EXPECT_EQ(inst->getModuleRef()->getName(), "M3");
    } else {
      ASSERT_TRUE(false) << "Unexpected instance";
    }
  }
}

TEST_F(InlineInstance, SymbolTableBasic) {
  // Grab handles to M1.i2.
  const auto inst_M1_i2 = top->getDef()->getInstances().at("i2");
  // Inline M1.i2.
  inlineInstance(inst_M1_i2);

  std::string flattentypes_str = "flattentypes";
  ctx->runPasses({"flattentypes", "verilog"}, {});

  auto table = ctx->getPassManager()->getSymbolTable();
  // Check module names (sanity check).
  EXPECT_EQ(table->getModuleName("M1"), "M1");
  EXPECT_EQ(table->getModuleName("M2"), "M2");
  EXPECT_EQ(table->getModuleName("M3"), "M3");
  EXPECT_EQ(table->getModuleName("M4"), "M4");
  EXPECT_EQ(table->getModuleName("M5"), "M5");
  EXPECT_EQ(table->getModuleName("M6"), "M6");
  // Check non-inlined instance names.
  VariantExpectEq(table->getInstanceName("M2", "i3"), std::string("i3"));
  VariantExpectEq(table->getInstanceName("M3", "i4"), std::string("i4"));
  VariantExpectEq(table->getInstanceName("M4", "i6"), std::string("i5"));
  VariantExpectEq(table->getInstanceName("M5", "i6"), std::string("i6"));
  // Check inlined instance.
  // NOTE(rsetaluri): Not exactly sure why the const_cast needs to appear this
  // away. Ostensibly, the type returned by
  // symbolTableInlinedInstanceSentinel(), and the type inside the variant are
  // both 'SymbolTableSentinel* const', but it seems a const gets lost in the
  // former.
  VariantExpectEq(
      table->getInstanceName("M1", "i2"),
      const_cast<const SymbolTableSentinel*>(
          symbolTableInlinedInstanceSentinel()));
  VariantExpectEq(
      table->getInlinedInstanceName("M1", "i2", "i3"),
      std::string("i2$i3"));
}

TEST_F(InlineInstance, SymbolTableTopDown) {
  // Grab handles to M1.i2.
  const auto inst_M1_i2 = top->getDef()->getInstances().at("i2");
  // Inline M1.i2.
  inlineInstance(inst_M1_i2);

  // Grab handles to M1.i2$i3.
  const auto inst_M1_i2dollari3 = top->getDef()->getInstances().at("i2$i3");
  // Inline M1.i2$i3.
  inlineInstance(inst_M1_i2dollari3);

  std::string flattentypes_str = "flattentypes";
  ctx->runPasses({"flattentypes", "verilog"}, {});

  auto table = ctx->getPassManager()->getSymbolTable();
  // Check inlined instance.
  // NOTE(rsetaluri): Not exactly sure why the const_cast needs to appear this
  // away. Ostensibly, the type returned by
  // symbolTableInlinedInstanceSentinel(), and the type inside the variant are
  // both 'SymbolTableSentinel* const', but it seems a const gets lost in the
  // former.
  VariantExpectEq(
      table->getInstanceName("M1", "i2"),
      const_cast<const SymbolTableSentinel*>(
          symbolTableInlinedInstanceSentinel()));
  // TODO(rsetaluri): Figure out the expectations here.
  // VariantExpectEq(
  //     table->getInlinedInstanceName("M1", "i2", "i3"),
  //     const_cast<const SymbolTableSentinel*>(
  //         symbolTableInlinedInstanceSentinel()));
  // VariantExpectEq(
  //     table->getInlinedInstanceName("M1", "i2$i3", "i4"),
  //     std::string("i2$i3$i4"));
}

}  // namespace
}  // namespace coreir

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
