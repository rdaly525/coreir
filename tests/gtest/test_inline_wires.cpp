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

void check_verilog(
  Context* context,
  std::string gold_file,
  bool ndarray = false) {
  context->runPasses(
    {"flattentypes" + std::string(ndarray ? " --ndarray" : ""),
     "verilog --inline"},
    {});
  assertPassEq(context, "verilog", gold_file);
}

TEST(VerilogInlineWireTest, TestBitWire) {
  Context* c = newContext();
  CoreIRLoadVerilog_corebit(c);
  load_file(c, "srcs/bit_wire.json");

  check_verilog(c, "golds/bit_wire.v");
  deleteContext(c);
}

TEST(VerilogInlineWireTest, TestBitsWire) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  load_file(c, "srcs/bits_wire.json");

  check_verilog(c, "golds/bits_wire.v");
  deleteContext(c);
}

TEST(VerilogInlineWireTest, TestNestedArraysWire) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  load_file(c, "srcs/nested_array_wire.json");

  check_verilog(c, "golds/nested_array_wire.v");
  deleteContext(c);
}

TEST(VerilogInlineWireTest, TestTupleWire) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  load_file(c, "srcs/tuple.json");

  check_verilog(c, "golds/tuple.v");
  deleteContext(c);
}

TEST(VerilogInlineWireTest, TestArrTupleWire) {
  Context* c = newContext();
  CoreIRLoadVerilog_corebit(c);
  CoreIRLoadVerilog_coreir(c);
  load_file(c, "srcs/arr_tuple.json");

  check_verilog(c, "golds/arr_tuple.v");
  deleteContext(c);
}

TEST(VerilogInlineWireTest, TestFanOut) {
  Context* c = newContext();
  CoreIRLoadVerilog_corebit(c);
  load_file(c, "srcs/fanout.json");

  check_verilog(c, "golds/fanout.v");
  deleteContext(c);
}

TEST(VerilogInlineWireTest, TestInstance) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  load_file(c, "srcs/bits_instance.json");

  check_verilog(c, "golds/bits_instance.v");
  deleteContext(c);
}

TEST(VerilogInlineWireTest, TestIndexSliceInline) {
  Context* c = newContext();
  CoreIRLoadVerilog_coreir(c);
  load_file(c, "srcs/index-slice-inline.json");

  check_verilog(c, "golds/index-slice-inline.v", true);
  deleteContext(c);
}

}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
