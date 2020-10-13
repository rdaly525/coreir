#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/definitions/memoryVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(MemoryTests, TestROM) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  Module* top;

  if (!loadFromFile(c, "srcs/rom.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"rungenerators",
                                           "removebulkconnections",
                                           "flattentypes",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/rom.v");
  deleteContext(c);
}

TEST(MemoryTests, TestIssue932) {
  // https://github.com/rdaly525/coreir/issues/932
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadLibrary_commonlib(c);
  Module* top;

  if (!loadFromFile(c, "srcs/camera_pipeline_dse1.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"rungenerators",
                                           "removebulkconnections",
                                           "flattentypes",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/camera_pipeline_dse1.v");
  deleteContext(c);
}

TEST(MemoryTests, TestSyncReadMem) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadVerilog_memory(c);
  Module* top;

  if (!loadFromFile(c, "srcs/sync_read_mem.json", &top)) { c->die(); }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {"rungenerators",
                                           "removebulkconnections",
                                           "flattentypes",
                                           "verilog --inline"};
  c->runPasses(passes, {});
  assertPassEq(c, "verilog", "golds/sync_read_mem.v");
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
