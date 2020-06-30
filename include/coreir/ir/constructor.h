#pragma once

#include "fwd_declare.h"

namespace CoreIR {

class Constructor {
  ModuleDef* def;

 public:
  Constructor(ModuleDef* def) : def(def) {}

#define DECLARE_BINARY_OP(name) Wireable* name(Wireable* in0, Wireable* in1);

  DECLARE_BINARY_OP(add)
  DECLARE_BINARY_OP(sub)
  DECLARE_BINARY_OP(and_)
  DECLARE_BINARY_OP(or_)
  DECLARE_BINARY_OP(xor_)
  DECLARE_BINARY_OP(shl)
  DECLARE_BINARY_OP(lshr)
  DECLARE_BINARY_OP(ashr)
  DECLARE_BINARY_OP(mul)
  DECLARE_BINARY_OP(udiv)
  DECLARE_BINARY_OP(urem)
  DECLARE_BINARY_OP(sdiv)
  DECLARE_BINARY_OP(srem)
  DECLARE_BINARY_OP(smod)

  // Macro also works for binary reduce ops
  DECLARE_BINARY_OP(eq)
  DECLARE_BINARY_OP(neq)
  DECLARE_BINARY_OP(slt)
  DECLARE_BINARY_OP(sgt)
  DECLARE_BINARY_OP(sle)
  DECLARE_BINARY_OP(sge)
  DECLARE_BINARY_OP(ult)
  DECLARE_BINARY_OP(ugt)
  DECLARE_BINARY_OP(ule)
  DECLARE_BINARY_OP(uge)

#undef DECLARE_BINARY_OP

#define DECLARE_UNARY_OP(name) Wireable* name(Wireable* in0);

  DECLARE_UNARY_OP(wire)
  DECLARE_UNARY_OP(not_)
  DECLARE_UNARY_OP(neg)

  // Unary Reduce
  DECLARE_UNARY_OP(andr)
  DECLARE_UNARY_OP(orr)
  DECLARE_UNARY_OP(xorr)

  Wireable* mux(Wireable* sel, Wireable* in0, Wireable* in1);
  Wireable* concat(Wireable* in0, Wireable* in1);
  Wireable* slice(Wireable* in0, uint lo, uint hi);
  Wireable* const_(int bits, int value);
  Wireable* const_(bool value);
  void term(Wireable* in0);

  Wireable* zext(Wireable* in0, uint extend_bits);
  Wireable* sext(Wireable* in0, uint extend_bits);

  Wireable* reg(Wireable* in0, uint init, Wireable* clk = nullptr);
  Wireable* reg_arst(
    Wireable* in0,
    uint init,
    Wireable* clk = nullptr,
    Wireable* rst = nullptr);
};

}  // namespace CoreIR
