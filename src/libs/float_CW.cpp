#include "coreir/libs/float.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(float_CW);

using namespace std;
using namespace CoreIR;

//This will only implement the float library for add and mul
Namespace* CoreIRLoadLibrary_float_CW(Context* c) {


  Namespace* fpcw = c->newNamespace("float_CW");
  
  Params floatParams = Params({
    {"exp_bits",c->Int()},
    {"frac_bits",c->Int()},
    {"ieee_compliance",c->Bool()}
  });
  
  auto tg = fp->newTypeGen(
    "binary",
    floatParams,
    [](Context* c, Values args) {
      uint exp_bits = args.at("exp_bits")->get<int>();
      uint frac_bits = args.at("frac_bits")->get<int>();
      uint width = 1+exp_bits+frac_bits;
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"a",c->Flip(ptype)},
        {"b",c->Flip(ptype)},
        {"rnd",c->BitIn()->Arr(3)},
        {"z",ptype},
        {"status",c->Bit()->Arr(8)}
      });
    }
  );
 
  mul = fp->newGeneratorDecl("mul",tg,floatParams);
  add = fp->newGeneratorDecl("add",tg,floatParams);

  //Add verilog to mul
  {
    json vjson;
    vjson["interface"] =  {
      "input [exp_bits+frac_bits:0] a",
      "input [exp_bits+frac_bits:0] b",
      "input [2:0] rnd",
      "output [exp_bits+frac_bits:0] z"
      "output [7:0] status"
    };
    vjson["definition"] = ""
    "wire [7:0] status;\n"
    "CW_fp_mult #(.sig_width(frac_bits), .exp_width(exp_bits), .ieee_compliance(ieee_compliance)) mul1 (.a(a),.b(b),.rnd(rnd),.z(out),.status(status));";
    mul->getMetaData()["verilog"] = vjson;
  }
  
  //Add verilog to add
  {
    json vjson;
    vjson["interface"] =  {
      "input [exp_bits+frac_bits:0] a",
      "input [exp_bits+frac_bits:0] b",
      "input [2:0] rnd",
      "output [exp_bits+frac_bits:0] z"
      "output [7:0] status"
    };
    vjson["definition"] = ""
    "wire [7:0] status;\n"
    "CW_fp_add #(.sig_width(frac_bits), .exp_width(exp_bits), .ieee_compliance(ieee_compliance)) mul1 (.a(a),.b(b),.rnd(rnd),.z(out),.status(status));";
    mul->getMetaData()["verilog"] = vjson;
  }
  if (c->hasNamespace("float")) {
    auto fns = c->getNamespace("float")
    fns->getGenerator("mul")->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      uint exp_bits = args.at("exp_bits")->get<int>();
      uint frac_bits = args.at("frac_bits")->get<int>();
      uint ieee_compliance = args.at("ieee_compliance")->get<bool>();
      if (frac_bits <10) {
        uint fbit_delta = 10-frac_bits;
        auto mi = def->addInstance("mi","float_CW",{{"exp_bits",args.at("exp_bits")},{"frac_bits",Const::make(c,10)},{"ieee_compliance",Const::make(c,false)}});
        auto a = concat(a,b)
      }
      else {
        def->addInstance("mi","float_CW",{{"exp_bits",args.at("exp_bits")},{"frac_bits",args.at("frac_bits")},{"ieee_compliance",Const::make(c,false)}});
        def->connect("self.in0","mi.a");
        def->connect("self.in1","mi.b");
        def->connect("mi.z","self.out");
      }

    });

  }
