// Needs to have the same lenght
// Needs to both be bitvector
#include "coreir/ir/constructor.h"
#include "coreir/common/utils.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
#include "coreir/ir/value.h"
#include "coreir/ir/wireable.h"

namespace CoreIR {

namespace {
bool isBitInArray(Wireable* in0) {
  auto type = in0->getType();
  return isBitArray(*type) && type->isOutput();
}

void check_binary_inputs(Wireable* in0, Wireable* in1) {
  ASSERT(
    isBitInArray(in0) && isBitInArray(in1),
    "Both inputs need to be a BitVector");
  uint len0 = in0->getType()->getSize();
  uint len1 = in0->getType()->getSize();
  ASSERT(len0 == len1, "BitVectors need to be same size");
}

Wireable* binaryOp(Wireable* in0, Wireable* in1, std::string name) {
  auto def = in0->getContainer();
  Instance* inst;
  if (isa<BitType>(in0->getType()) && isa<BitType>(in1->getType())) {
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "corebit." + name);
  }
  else {
    check_binary_inputs(in0, in1);
    uint bv_len = in0->getType()->getSize();
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "coreir." + name,
      {{"width", Const::make(in0->getContext(), bv_len)}});
  }
  def->connect(in0, inst->sel("in0"));
  def->connect(in1, inst->sel("in1"));
  return inst->sel("out");
}

Wireable* unaryOp(Wireable* in0, std::string name) {
  auto def = in0->getContainer();
  Instance* inst;
  if (isa<BitType>(in0->getType())) {
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "corebit." + name);
  }
  else {
    ASSERT(isBitInArray(in0), "input needs to be bit or bit array");
    uint bv_len = in0->getType()->getSize();
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "coreir." + name,
      {{"width", Const::make(in0->getContext(), bv_len)}});
  }
  def->connect(in0, inst->sel("in"));
  return inst->sel("out");
}

}  // namespace

#define DEFINE_BINARY_OP(fun_name, coreir_name)                                \
  Wireable* Constructor::fun_name(Wireable* in0, Wireable* in1) {              \
    return binaryOp(in0, in1, #coreir_name);                                   \
  }

#define BINARY_OP1(name) DEFINE_BINARY_OP(name, name)
#define BINARY_OP2(name) DEFINE_BINARY_OP(name##_, name)
BINARY_OP1(add)
BINARY_OP1(sub)
BINARY_OP2(and)
BINARY_OP2(or)
BINARY_OP2(xor)
BINARY_OP1(shl)
BINARY_OP1(lshr)
BINARY_OP1(ashr)
BINARY_OP1(mul)
BINARY_OP1(udiv)
BINARY_OP1(urem)
BINARY_OP1(sdiv)
BINARY_OP1(srem)
BINARY_OP1(smod)

// Macro also works for binary reduce ops
BINARY_OP1(eq)
BINARY_OP1(neq)
BINARY_OP1(slt)
BINARY_OP1(sgt)
BINARY_OP1(sle)
BINARY_OP1(sge)
BINARY_OP1(ult)
BINARY_OP1(ugt)
BINARY_OP1(ule)
BINARY_OP1(uge)

#undef BINARY_OP1
#undef BINARY_OP2
#undef DEFINE_BINARY_OP

#define DEFINE_UNARY_OP(fun_name, coreir_name)                                 \
  Wireable* Constructor::fun_name(Wireable* in0) {                             \
    return unaryOp(in0, #coreir_name);                                         \
  }

#define UNARY_OP1(name) DEFINE_UNARY_OP(name, name)
#define UNARY_OP2(name) DEFINE_UNARY_OP(name##_, name)

UNARY_OP1(wire)
UNARY_OP2(not)
UNARY_OP1(neg)

// Unary Reduce
UNARY_OP1(andr)
UNARY_OP1(orr)
UNARY_OP1(xorr)

#undef UNARY_OP1
#undef UNARY_OP2
#undef DEFINE_UNARY_OP

// Mux
Wireable* Constructor::mux(Wireable* sel, Wireable* in0, Wireable* in1) {
  ASSERT(isa<BitType>(sel->getType()), "sel needs to be a Bit");
  auto def = in0->getContainer();
  Instance* inst;
  if (isa<BitType>(in0->getType()) && isa<BitType>(in1->getType())) {
    inst = def->addInstance(def->generateUniqueInstanceName(), "corebit.mux");
  }
  else {
    check_binary_inputs(in0, in1);
    uint bv_len = in0->getType()->getSize();
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "coreir.mux",
      {{"width", Const::make(in0->getContext(), bv_len)}});
  }
  def->connect(in0, inst->sel("in0"));
  def->connect(in1, inst->sel("in1"));
  def->connect(sel, inst->sel("sel"));
  return inst->sel("out");
}

// Const and Term
Wireable* Constructor::const_(int bits, int value) {
  auto c = this->def->getContext();
  auto inst = this->def->addInstance(
    def->generateUniqueInstanceName(),
    "coreir.const",
    {{"width", Const::make(c, bits)}},
    {{"value", Const::make(c, bits, value)}});
  return inst->sel("out");
}

// For bit const
Wireable* Constructor::const_(bool value) {
  auto c = this->def->getContext();
  auto inst = this->def->addInstance(
    def->generateUniqueInstanceName(),
    "corebit.const",
    {{"value", Const::make(c, value)}});
  return inst->sel("out");
}

void Constructor::term(Wireable* in0) {
  auto def = in0->getContainer();
  Instance* inst;
  if (isa<BitType>(in0->getType())) {
    inst = def->addInstance(def->generateUniqueInstanceName(), "corebit.term");
  }
  else {
    ASSERT(isBitInArray(in0), "input needs to be bit or bit array");
    uint len = in0->getType()->getSize();
    auto c = def->getContext();
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "coreir.term",
      {{"width0", Const::make(c, len)}});
  }
  def->connect(in0, inst->sel("in"));
}

// Concat and slice
Wireable* Constructor::concat(Wireable* in0, Wireable* in1) {
  auto def = in0->getContainer();
  Instance* inst;
  if (isa<BitType>(in0->getType()) && isa<BitType>(in1->getType())) {
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "corebit.cocnat");
  }
  else {
    ASSERT(
      isBitInArray(in0) && isBitInArray(in1),
      "Both inputs need to be a BitVector");
    uint len0 = in0->getType()->getSize();
    uint len1 = in1->getType()->getSize();
    auto c = def->getContext();
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "coreir.concat",
      {{"width0", Const::make(c, len0)}, {"width1", Const::make(c, len1)}});
  }
  def->connect(in0, inst->sel("in0"));
  def->connect(in1, inst->sel("in1"));
  return inst->sel("out");
}

Wireable* Constructor::slice(Wireable* in0, uint lo, uint hi) {
  ASSERT(isBitInArray(in0), "input needs to be a BitVector");
  uint bits = in0->getType()->getSize();
  ASSERT(hi > lo && hi <= bits, "Bad range for slice");
  auto def = in0->getContainer();
  auto c = def->getContext();
  auto inst = def->addInstance(
    def->generateUniqueInstanceName(),
    "coreir.slice",
    {{"width", Const::make(c, bits)},
     {"lo", Const::make(c, lo)},
     {"hi", Const::make(c, hi)}});
  def->connect(in0, inst->sel("in"));
  return inst->sel("out");
}

// sext and zext
#define EXT_OP(fun_name)                                                       \
  Wireable* Constructor::fun_name(Wireable* in0, uint extend_bits) {           \
    ASSERT(isBitInArray(in0), "input needs to be a BitVector");                \
    uint bits = in0->getType()->getSize();                                     \
    ASSERT(extend_bits >= bits, "Cannot extend");                              \
    auto def = in0->getContainer();                                            \
    auto c = def->getContext();                                                \
    auto inst = def->addInstance(                                              \
      def->generateUniqueInstanceName(),                                       \
      "coreir." #fun_name,                                                     \
      {{"width_in", Const::make(c, bits)},                                     \
       {"width_out", Const::make(c, extend_bits)}});                           \
    def->connect(in0, inst->sel("in"));                                        \
    return inst->sel("out");                                                   \
  }

EXT_OP(sext)
EXT_OP(zext)

#undef EXT_OP

// Register
Wireable* Constructor::reg(Wireable* in0, uint init, Wireable* clk) {
  auto def = in0->getContainer();
  Instance* inst;
  if (isa<BitType>(in0->getType())) {
    inst = def->addInstance(def->generateUniqueInstanceName(), "corebit.reg");
  }
  else {
    ASSERT(isBitInArray(in0), "input needs to be a BitVector");
    uint bits = in0->getType()->getSize();
    auto c = this->def->getContext();
    inst = this->def->addInstance(
      def->generateUniqueInstanceName(),
      "coreir.reg",
      {{"width", Const::make(c, bits)}},
      {{"init", Const::make(c, bits, init)}});
  }
  def->connect(in0, inst->sel("in"));
  if (clk != nullptr) { def->connect(clk, inst->sel("clk")); }
  return inst->sel("out");
}

Wireable* Constructor::reg_arst(
  Wireable* in0,
  uint init,
  Wireable* clk,
  Wireable* rst) {
  auto def = in0->getContainer();
  Instance* inst;
  if (isa<BitType>(in0->getType())) {
    inst = def->addInstance(
      def->generateUniqueInstanceName(),
      "corebit.reg_arst");
  }
  else {
    ASSERT(isBitInArray(in0), "input needs to be a BitVector");
    uint bits = in0->getType()->getSize();
    auto c = this->def->getContext();
    inst = this->def->addInstance(
      def->generateUniqueInstanceName(),
      "coreir.reg_arst",
      {{"width", Const::make(c, bits)}},
      {{"init", Const::make(c, bits, init)}});
  }
  def->connect(in0, inst->sel("in"));
  if (clk != nullptr) { def->connect(clk, inst->sel("clk")); }

  if (rst != nullptr) { def->connect(rst, inst->sel("arst")); }
  return inst->sel("out");
}

}  // namespace CoreIR
