#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {
TEST(MantleVerilogTests, TestConcatT) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_concat.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_concat.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestSliceT) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_slice.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_slice.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestGetT) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_get.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_get.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestSanitize) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_sanitize.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_sanitize.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestLift) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_lift.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_lift.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestConcatN) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_concat_n.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_concat_n.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestSlices) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_slices.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_slices.v");
  deleteContext(c);
}

TEST(MantleVerilogTests, TestGets) {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "srcs/mantle_gets.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes --ndarray",
    "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/mantle_gets.v");
  deleteContext(c);
}
}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
