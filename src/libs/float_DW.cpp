#include "coreir/libs/float_DW.h"
#include "coreir/ir/constructor.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(float_DW);

using namespace std;
using namespace CoreIR;

// This will only implement the float library for add and mul
Namespace* CoreIRLoadLibrary_float_DW(Context* c) {

  Namespace* fpdw = c->newNamespace("float_DW");
  Params floatParams = Params({{"exp_width", c->Int()},
                               {"sig_width", c->Int()},
                               {"ieee_compliance", c->Bool()}});

  auto binary_tg = fpdw->newTypeGen(
    "binary",
    floatParams,
    [](Context* c, Values args) {
      uint exp_width = args.at("exp_width")->get<int>();
      uint sig_width = args.at("sig_width")->get<int>();
      uint width = 1 + exp_width + sig_width;
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({{"a", c->Flip(ptype)},
                        {"b", c->Flip(ptype)},
                        {"rnd", c->BitIn()->Arr(3)},
                        {"z", ptype},
                        {"status", c->Bit()->Arr(8)}});
    });

  auto muldw = fpdw->newGeneratorDecl("fp_mul", binary_tg, floatParams);
  auto adddw = fpdw->newGeneratorDecl("fp_add", binary_tg, floatParams);

  // Add verilog to mul
  {
    json vjson;
    vjson["interface"] = {"input [exp_width+sig_width:0] a",
                          "input [exp_width+sig_width:0] b",
                          "input [2:0] rnd",
                          "output [exp_width+sig_width:0] z",
                          "output [7:0] status"};
    vjson["definition"] =
      ""
      "DW_fp_mult #(.sig_width(sig_width), .exp_width(exp_width), "
      ".ieee_compliance(ieee_compliance)) mul_inst "
      "(.a(a),.b(b),.rnd(rnd),.z(z),.status(status));";
    muldw->getMetaData()["verilog"] = vjson;
  }

  // Add verilog to add
  {
    json vjson;
    vjson["interface"] = {"input [exp_width+sig_width:0] a",
                          "input [exp_width+sig_width:0] b",
                          "input [2:0] rnd",
                          "output [exp_width+sig_width:0] z",
                          "output [7:0] status"};
    vjson["definition"] =
      ""
      "DW_fp_add #(.sig_width(sig_width), .exp_width(exp_width), "
      ".ieee_compliance(ieee_compliance)) add_inst "
      "(.a(a),.b(b),.rnd(rnd),.z(z),.status(status));";
    adddw->getMetaData()["verilog"] = vjson;
  }

  if (!c->hasNamespace("float")) { c->getLibraryManager()->loadLib("float"); }

  // load the definition of float.add and float.mul
  auto fp = c->getNamespace("float");
  fp->getGenerator("add")->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      auto add = def->addInstance(
        "ai",
        "float_DW.fp_add",
        {{"exp_width", args.at("exp_bits")},
         {"sig_width", args.at("frac_bits")},
         {"ieee_compliance", Const::make(c, false)}});
      auto io = def->getInterface();
      auto C = Constructor(def);
      def->connect(io->sel("in0"), add->sel("a"));
      def->connect(io->sel("in1"), add->sel("b"));
      def->connect(C.const_(3, 0), add->sel("rnd"));
      def->connect(add->sel("z"), io->sel("out"));
    });

  fp->getGenerator("mul")->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      auto add = def->addInstance(
        "mi",
        "float_DW.fp_mul",
        {{"exp_width", args.at("exp_bits")},
         {"sig_width", args.at("frac_bits")},
         {"ieee_compliance", Const::make(c, false)}});
      auto io = def->getInterface();
      auto C = Constructor(def);
      def->connect(io->sel("in0"), add->sel("a"));
      def->connect(io->sel("in1"), add->sel("b"));
      def->connect(C.const_(3, 0), add->sel("rnd"));
      def->connect(add->sel("z"), io->sel("out"));
    });

  return fpdw;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(float_DW)
