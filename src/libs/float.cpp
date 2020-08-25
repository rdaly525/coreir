#include "coreir/libs/float.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(float);

using namespace std;
using namespace CoreIR;

// Rounding Mode:
//  Round Nearest Ties to Even
//  Round Nearest Ties to Away
//  Round Toward Positive
//  Round Toward Negative
//  Round Toward Zero

// ebits : Int , mbits : Int
// Represents number of exponent bits
// Constraint ebits > 0, mbits > 0

// Ops
// fp.abs
// fp.neg
// fp.add
// fp.sub
// fp.mul
// fp.div
// fp.fma
// fp.sqr
// fp.rem
// fp.round
// fp.min
// fp.max
// fp.le
// fp.lt
// fp.ge
// fp.gt
// fp.eq






// fp.isNormal
// fp.isSubnormal
// fp.isZero
// fp.isInfinite
// fp.isNaN
// fp.isNegative
// fp.isPositive

// Conversion Functions
// fp.fp_to_fp
// fp.fp_to_sint
// fp.fp_to_uint
// fp.sint_to_fp
// fp.uint_to_fp

//Halide FP ops
//add
//sub
//mul
//div
//mod
//neg
//lt
//le
//gt
//ge
//ne
//eq
//ceil
//flr
//rnd
//max
//min
//tanh
//exp
//log
//power

//atan2

//sqrt
//asin
//acos
//atan
//sin
//cos
//tan




Namespace* CoreIRLoadLibrary_float(Context* c) {
  Namespace* fp = c->newNamespace("float");

  Params floatParams = Params(
    {{"exp_bits", c->Int()}, {"frac_bits", c->Int()}});

  // Common Function types
  fp->newTypeGen("unary", floatParams, [](Context* c, Values args) {
    uint exp_bits = args.at("exp_bits")->get<int>();
    uint frac_bits = args.at("frac_bits")->get<int>();
    uint width = 1 + exp_bits + frac_bits;
    Type* ptype = c->Bit()->Arr(width);
    return c->Record({{"in", c->Flip(ptype)}, {"out", ptype}});
  });
  fp->newTypeGen("binary", floatParams, [](Context* c, Values args) {
    uint exp_bits = args.at("exp_bits")->get<int>();
    uint frac_bits = args.at("frac_bits")->get<int>();
    uint width = 1 + exp_bits + frac_bits;
    Type* ptype = c->Bit()->Arr(width);
    return c->Record(
      {{"in0", c->Flip(ptype)}, {"in1", c->Flip(ptype)}, {"out", ptype}});
  });

  fp->newTypeGen("binaryReduce", floatParams, [](Context* c, Values args) {
    uint exp_bits = args.at("exp_bits")->get<int>();
    uint frac_bits = args.at("frac_bits")->get<int>();
    uint width = 1 + exp_bits + frac_bits;
    Type* ptype = c->Bit()->Arr(width);
    return c->Record(
      {{"in0", c->Flip(ptype)}, {"in1", c->Flip(ptype)}, {"out", c->Bit()}});
  });

  fp->newTypeGen("muxType", floatParams, [](Context* c, Values args) {
    uint exp_bits = args.at("exp_bits")->get<int>();
    uint frac_bits = args.at("frac_bits")->get<int>();
    uint width = 1 + exp_bits + frac_bits;
    Type* ptype = c->Bit()->Arr(width);
    return c->Record({{"in0", c->Flip(ptype)},
                      {"in1", c->Flip(ptype)},
                      {"sel", c->BitIn()},
                      {"out", ptype}});
  });

  vector<string> unaryOps = {"neg", "sqr", "flr", "ceil", "rnd", "sqrt", "exp", "ln", "sin", "cos", "tan", "asin", "acos", "atan", "tanh"};
  vector<string> binaryOps =
    {"abs", "add", "sub", "mul", "div", "rem", "min", "max", "atan2", "power"};
  vector<string> binaryReduceOps = {"le", "lt", "ge", "gt", "eq", "neq"};

  for (auto op : unaryOps) {
    TypeGen* tg = fp->getTypeGen("unary");
    fp->newGeneratorDecl(op, tg, floatParams);
  }
  for (auto op : binaryOps) {
    TypeGen* tg = fp->getTypeGen("binary");
    fp->newGeneratorDecl(op, tg, floatParams);
  }
  for (auto op : binaryReduceOps) {
    TypeGen* tg = fp->getTypeGen("binaryReduce");
    fp->newGeneratorDecl(op, tg, floatParams);
  }
  fp->newGeneratorDecl("mux", fp->getTypeGen("muxType"), floatParams);

  return fp;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(float)
