#include "gtest/gtest.h"
#include "coreir.h"
#include "coreir/common/logging_lite.hpp"
#include "coreir/ir/instance_graph_logger.hpp"

namespace CoreIR {
namespace {

class IGL : public ::testing::Test {
 public:
  IGL() = default;

  void SetUp() override {
    ctx = newContext();
    ctx->getPassManager()->setDebug(true);
    if (!loadFromFile(ctx, "../../tests/gtest/srcs/simple_hierarchy.json", &top)) ctx->die();
    assert(top != nullptr);
    ctx->setTop(top->getRefName());
    igl = ctx->getPassManager()->getInstanceGraphLogger();
  }

  void TearDown() override {
    deleteContext(ctx);
  }

 protected:
  Context* ctx = nullptr;
  Module* top = nullptr;
  InstanceGraphLogger* igl = nullptr;
};


using InstancePath = SelectPath;

TEST_F(IGL, None) {
  InstancePath query = {"i2", "i3", "i4", "i5"};
  InstancePath expect = {"i2", "i3", "i4", "i5"};
  ASSERT_EQ(igl->getInstancePath("global.M1", query), expect);
}

//inline i2
TEST_F(IGL, I2) {
  auto m1 = ctx->getModule("global.M1");
  auto i2 = m1->getDef()->getInstances().at("i2");
  inlineInstance(i2);

  InstancePath query = {"i2", "i3", "i4", "i5"};
  InstancePath expect = {"i2$i3", "i4", "i5"};
  ASSERT_EQ(igl->getInstancePath("global.M1", query), expect);
}

//inline i3
TEST_F(IGL, I3) {
  auto m2 = ctx->getModule("global.M2");
  auto i3 = m2->getDef()->getInstances().at("i3");
  inlineInstance(i3);

  InstancePath query = {"i2", "i3", "i4", "i5"};
  InstancePath expect = {"i2", "i3$i4", "i5"};
  ASSERT_EQ(igl->getInstancePath("M1", query), expect);
}

//Inline i3, then i2
TEST_F(IGL, I32) {

  auto m2 = ctx->getModule("global.M2");
  auto i3 = m2->getDef()->getInstances().at("i3");
  inlineInstance(i3);

  auto m1 = ctx->getModule("global.M1");
  auto i2 = m1->getDef()->getInstances().at("i2");
  inlineInstance(i2);

  InstancePath query = {"i2", "i3", "i4", "i5"};
  InstancePath expect = {"i2$i3$i4", "i5"};
  ASSERT_EQ(igl->getInstancePath("M1", query), expect);
}

//Inline i2, then i3
TEST_F(IGL, I23) {
  auto m1 = ctx->getModule("global.M1");
  auto i2 = m1->getDef()->getInstances().at("i2");
  inlineInstance(i2);

  auto i3 = m1->getDef()->getInstances().at("i2$i3");
  inlineInstance(i3);

  InstancePath query = {"i2", "i3", "i4", "i5"};
  InstancePath expect = {"i2$i3$i4", "i5"};
  ASSERT_EQ(igl->getInstancePath("M1", query), expect);
}

}  // namespace
}  // namespace coreir

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
