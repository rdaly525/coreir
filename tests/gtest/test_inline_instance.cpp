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
    ctx->setDebug(true);
    if (!loadFromFile(ctx, "srcs/simple_hierarchy.json", &top)) ctx->die();
    assert(top != nullptr);
    ctx->setTop(top->getRefName());
  }

  void TearDown() override {
    if (table != nullptr) std::cout << table->json() << std::endl;
    deleteContext(ctx);
  }

 protected:
  Context* ctx = nullptr;
  Module* top = nullptr;
  SymbolTableInterface* table = nullptr;
  SymbolTableSentinel* const empty = symbolTableEmptySentinel();
  SymbolTableSentinel* const inlined = symbolTableInlinedInstanceSentinel();
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

  table = ctx->getPassManager()->getSymbolTable();
  table->getLogger()->finalize();
  // Check module names (sanity check).
  EXPECT_EQ(table->getModuleName("M1"), "M1");
  // This won't work since there are no longer instances of M2:
  //   EXPECT_EQ(table->getModuleName("M2"), "M2");
  EXPECT_EQ(table->getModuleName("M3"), "M3");
  EXPECT_EQ(table->getModuleName("M4"), "M4");
  EXPECT_EQ(table->getModuleName("M5"), "M5");
  EXPECT_EQ(table->getModuleName("M6"), "M6");
  // Check non-inlined instance names.
  EXPECT_EQ(table->getInstanceName("M2", "i3"), std::make_tuple(empty, "i3"));
  EXPECT_EQ(table->getInstanceName("M3", "i4"), std::make_tuple(empty, "i4"));
  EXPECT_EQ(table->getInstanceName("M4", "i5"), std::make_tuple(empty, "i5"));
  EXPECT_EQ(table->getInstanceName("M5", "i6"), std::make_tuple(empty, "i6"));
  // Check inlined instance.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M1", "i2")), inlined);
  EXPECT_EQ(table->getInlinedInstanceName("M1", "i2", "i3"),
            std::make_tuple(empty, "i2$i3"));
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

  table = ctx->getPassManager()->getSymbolTable();
  table->getLogger()->finalize();
  // Check M1.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M1", "i2")), inlined);
  auto ret = table->getInlinedInstanceName("M1", "i2", "i3");
  EXPECT_EQ(std::get<0>(ret), inlined);
  auto key = std::get<1>(ret);
  EXPECT_EQ(table->getInlinedInstanceName("M1", key, "i4"),
            std::make_tuple(empty, "i2$i3$i4"));
}

TEST_F(InlineInstance, SymbolTableTopDownMultilevel) {
  // Grab handles to M1.i2.
  const auto inst_M1_i2 = top->getDef()->getInstances().at("i2");
  // Inline M1.i2.
  inlineInstance(inst_M1_i2);

  // Grab handles to M1.i2$i3.
  const auto inst_M1_i2dollari3 = top->getDef()->getInstances().at("i2$i3");
  // Inline M1.i2$i3.
  inlineInstance(inst_M1_i2dollari3);

  // Grab handles to M1.i2$i3$i4.
  const auto inst_M1_i2dollari3dollari4 = top->getDef()->
      getInstances().at("i2$i3$i4");
  // Inline M1.i2$i3$i4.
  inlineInstance(inst_M1_i2dollari3dollari4);

  std::string flattentypes_str = "flattentypes";
  ctx->runPasses({"flattentypes", "verilog"}, {});

  table = ctx->getPassManager()->getSymbolTable();
  table->getLogger()->finalize();
  // Check M1.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M1", "i2")), inlined);
  auto ret = table->getInlinedInstanceName("M1", "i2", "i3");
  EXPECT_EQ(std::get<0>(ret), inlined);
  auto key = std::get<1>(ret);
  ret = table->getInlinedInstanceName("M1", key, "i4");
  EXPECT_EQ(std::get<0>(ret), inlined);
  key = std::get<1>(ret);
  EXPECT_EQ(table->getInlinedInstanceName("M1", key, "i5"),
            std::make_tuple(empty, "i2$i3$i4$i5"));
}

TEST_F(InlineInstance, SymbolTableBottomUp) {
  // Grab handles to M2.i3.
  const auto M2 = ctx->getModule("global.M2");
  const auto inst_M2_i3 = M2->getDef()->getInstances().at("i3");
  // Inline M2.i3.
  inlineInstance(inst_M2_i3);

  // Grab handles to M1.i2.
  const auto inst_M1_i2 = top->getDef()->getInstances().at("i2");
  // Inline M1.i2.
  inlineInstance(inst_M1_i2);

  std::string flattentypes_str = "flattentypes";
  ctx->runPasses({"flattentypes", "verilog"}, {});

  table = ctx->getPassManager()->getSymbolTable();
  table->getLogger()->finalize();
  // Check M1.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M1", "i2")), inlined);
  auto ret = table->getInlinedInstanceName("M1", "i2", "i3");
  EXPECT_EQ(std::get<0>(ret), inlined);
  auto key = std::get<1>(ret);
  EXPECT_EQ(table->getInlinedInstanceName("M1", key, "i4"),
            std::make_tuple(empty, "i2$i3$i4"));
  // Check M2.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M2", "i3")), inlined);
  EXPECT_EQ(table->getInlinedInstanceName("M2", "i3", "i4"),
            std::make_tuple(empty, "i3$i4"));
}

TEST_F(InlineInstance, SymbolTableBottomUpMultilevel) {
  // Grab handles to M3.i4.
  const auto M3 = ctx->getModule("global.M3");
  const auto inst_M3_i4 = M3->getDef()->getInstances().at("i4");
  // Inline M3.i4.
  inlineInstance(inst_M3_i4);

  // Grab handles to M2.i3.
  const auto M2 = ctx->getModule("global.M2");
  const auto inst_M2_i3 = M2->getDef()->getInstances().at("i3");
  // Inline M2.i3.
  inlineInstance(inst_M2_i3);

  // Grab handles to M1.i2.
  const auto inst_M1_i2 = top->getDef()->getInstances().at("i2");
  // Inline M1.i2.
  inlineInstance(inst_M1_i2);

  std::string flattentypes_str = "flattentypes";
  ctx->runPasses({"flattentypes", "verilog"}, {});

  table = ctx->getPassManager()->getSymbolTable();
  table->getLogger()->finalize();

  // Check inlined instances for M1.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M1", "i2")), inlined);
  auto ret = table->getInlinedInstanceName("M1", "i2", "i3");
  EXPECT_EQ(std::get<0>(ret), inlined);
  auto key = std::get<1>(ret);
  ret = table->getInlinedInstanceName("M1", key, "i4");
  EXPECT_EQ(std::get<0>(ret), inlined);
  key = std::get<1>(ret);
  EXPECT_EQ(table->getInlinedInstanceName("M1", key, "i5"),
            std::make_tuple(empty, "i2$i3$i4$i5"));
  // Check M2.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M2", "i3")), inlined);
  ret = table->getInlinedInstanceName("M2", "i3", "i4");
  EXPECT_EQ(std::get<0>(ret), inlined);
  key = std::get<1>(ret);
  EXPECT_EQ(table->getInlinedInstanceName("M2", key, "i5"),
            std::make_tuple(empty, "i3$i4$i5"));
  // Check M3.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M3", "i4")), inlined);
  EXPECT_EQ(table->getInlinedInstanceName("M3", "i4", "i5"),
            std::make_tuple(empty, "i4$i5"));
}

TEST_F(InlineInstance, SymbolTableTopDownAndBottomUp) {
  // Grab handles to M1.i2.
  const auto inst_M1_i2 = top->getDef()->getInstances().at("i2");
  // Inline M1.i2.
  inlineInstance(inst_M1_i2);

  // Grab handles to M3.i4.
  const auto M3 = ctx->getModule("global.M3");
  const auto inst_M3_i4 = M3->getDef()->getInstances().at("i4");
  // Inline M3.i4.
  inlineInstance(inst_M3_i4);

  // Grab handles to M1.i2$i3.
  const auto inst_M1_i2dollari3 = top->getDef()->getInstances().at("i2$i3");
  // Inline M1.i2$i3.
  inlineInstance(inst_M1_i2dollari3);

  std::string flattentypes_str = "flattentypes";
  ctx->runPasses({"flattentypes", "verilog"}, {});

  table = ctx->getPassManager()->getSymbolTable();
  table->getLogger()->finalize();

  // Check M1.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M1", "i2")), inlined);
  auto ret = table->getInlinedInstanceName("M1", "i2", "i3");
  EXPECT_EQ(std::get<0>(ret), inlined);
  auto key = std::get<1>(ret);
  ret = table->getInlinedInstanceName("M1", key, "i4");
  EXPECT_EQ(std::get<0>(ret), inlined);
  key = std::get<1>(ret);
  EXPECT_EQ(table->getInlinedInstanceName("M1", key, "i5"),
            std::make_tuple(empty, "i2$i3$i4$i5"));
  // Check M2.
  EXPECT_EQ(table->getInstanceName("M2", "i3"), std::make_tuple(empty, "i3"));
  // Check M3.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M3", "i4")), inlined);
  EXPECT_EQ(table->getInlinedInstanceName("M3", "i4", "i5"),
            std::make_tuple(empty, "i4$i5"));
}

TEST_F(InlineInstance, SymbolTableBottomUpAndTopDown) {
  // Grab handles to M3.i4.
  const auto M3 = ctx->getModule("global.M3");
  const auto inst_M3_i4 = M3->getDef()->getInstances().at("i4");
  // Inline M3.i4.
  inlineInstance(inst_M3_i4);

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

  table = ctx->getPassManager()->getSymbolTable();
  table->getLogger()->finalize();

  // Check M1.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M1", "i2")), inlined);
  auto ret = table->getInlinedInstanceName("M1", "i2", "i3");
  EXPECT_EQ(std::get<0>(ret), inlined);
  auto key = std::get<1>(ret);
  ret = table->getInlinedInstanceName("M1", key, "i4");
  EXPECT_EQ(std::get<0>(ret), inlined);
  key = std::get<1>(ret);
  EXPECT_EQ(table->getInlinedInstanceName("M1", key, "i5"),
            std::make_tuple(empty, "i2$i3$i4$i5"));
  // Check M2.
  EXPECT_EQ(table->getInstanceName("M2", "i3"), std::make_tuple(empty, "i3"));
  // Check M3.
  EXPECT_EQ(std::get<0>(table->getInstanceName("M3", "i4")), inlined);
  EXPECT_EQ(table->getInlinedInstanceName("M3", "i4", "i5"),
            std::make_tuple(empty, "i4$i5"));
}

}  // namespace
}  // namespace coreir

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
