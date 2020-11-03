#include "coreir/libs/float_CW.h"
#include "coreir/ir/constructor.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(float_CW);

using namespace std;
using namespace CoreIR;

// This will only implement the float library for add and mul
Namespace* CoreIRLoadLibrary_float_CW(Context* c) {

  Namespace* fpcw = c->newNamespace("float_CW");
  Params floatParams = Params({{"exp_bits", c->Int()},
                               {"frac_bits", c->Int()},
                               {"ieee_compliance", c->Bool()}});

  auto add_tg = fpcw->newTypeGen(
    "addtype",
    floatParams,
    [](Context* c, Values args) {
      uint exp_bits = args.at("exp_bits")->get<int>();
      uint frac_bits = args.at("frac_bits")->get<int>();
      uint width = 1 + exp_bits + frac_bits;
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({{"a", c->Flip(ptype)},
                        {"b", c->Flip(ptype)},
                        {"rnd", c->BitIn()->Arr(3)},
                        {"z", ptype},
                        {"status", c->Bit()->Arr(8)}});
    });
  auto mul_tg = fpcw->newTypeGen(
    "mul_tg",
    floatParams,
    [](Context* c, Values args) {
      uint exp_bits = args.at("exp_bits")->get<int>();
      uint frac_bits = args.at("frac_bits")->get<int>();
      // This module is known to be unsafe/incorrect for < 10 frac
      // bits. However, we are still using it with a slight workaround, and
      // therefore disable the assertion.
      // ASSERT(
      //   frac_bits >= 10,
      //   "Cannot instantiate multiplier less than 10 bits");
      uint width = 1 + exp_bits + frac_bits;
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({{"a", c->Flip(ptype)},
                        {"b", c->Flip(ptype)},
                        {"rnd", c->BitIn()->Arr(3)},
                        {"z", ptype},
                        {"status", c->Bit()->Arr(8)}});
    });

  auto mulcw = fpcw->newGeneratorDecl("mul", mul_tg, floatParams);
  auto mulcw_hack = fpcw->newGeneratorDecl("mul_hack", mul_tg, floatParams);
  auto addcw = fpcw->newGeneratorDecl("add", add_tg, floatParams);

  // Add verilog to mul
  {
    json vjson;
    vjson["interface"] = {"input [exp_bits+frac_bits:0] a",
                          "input [exp_bits+frac_bits:0] b",
                          "input [2:0] rnd",
                          "output [exp_bits+frac_bits:0] z",
                          "output [7:0] status"};
    vjson["definition"] =
      ""
      "wire [7:0] status;\n"
      "CW_fp_mult #(.sig_width(frac_bits), .exp_width(exp_bits), "
      ".ieee_compliance(ieee_compliance)) mul_inst "
      "(.a(a),.b(b),.rnd(rnd),.z(out),.status(status));";
    mulcw->getMetaData()["verilog"] = vjson;
  }

  //rnd should be passed as 3'h1
  // Special case the verilog for BFloat16 mul
  {
    json vjson;
    vjson["interface"] = {"input [exp_bits+frac_bits:0] a",
                          "input [exp_bits+frac_bits:0] b",
                          "input [2:0] rnd",
                          "output [exp_bits+frac_bits:0] z",
                          "output [7:0] status"};
    vjson["definition"] = R"(
wire [exp_bits+frac_bits:0] int_out;
wire [2:0] results_x;
reg sign;
reg [exp_bits-1:0] exp;
reg [frac_bits:0] frac;

CW_fp_mult #(.sig_width(frac_bits+3), .exp_width(exp_bits), .ieee_compliance(ieee_compliance)) mul1 (.a({a,3'h0}),.b({b,3'h0}),.rnd(rnd),.z({int_out,results_x}),.status(status));

always @(*) begin
  sign = int_out[exp_bits+frac_bits];
  exp  = int_out[exp_bits+frac_bits-1:frac_bits];
  frac = {1'b0,int_out[frac_bits-1:0]};
  if ((results_x[2]&(results_x[1] | results_x[0])) | (int_out[0] & results_x[2])) begin
    frac = frac + 1'd1;
    if (~&exp) begin
      exp = exp + {{(exp_bits-1){1'b0}},frac[frac_bits]};
    end
  end
end
assign z = {sign, exp, frac[frac_bits-1:0]};
)";
    mulcw_hack->getMetaData()["verilog"] = vjson;
  }

  // Add verilog to add
  {
    json vjson;
    vjson["interface"] = {"input [exp_bits+frac_bits:0] a",
                          "input [exp_bits+frac_bits:0] b",
                          "input [2:0] rnd",
                          "output [exp_bits+frac_bits:0] z",
                          "output [7:0] status"};
    vjson["definition"] =
      ""
      "CW_fp_add #(.sig_width(frac_bits), .exp_width(exp_bits), "
      ".ieee_compliance(ieee_compliance)) add_inst "
      "(.a(a),.b(b),.rnd(rnd),.z(z),.status(status));";
    addcw->getMetaData()["verilog"] = vjson;
  }

  if (!c->hasNamespace("float")) { c->getLibraryManager()->loadLib("float"); }

  // Load the def for add
  auto fp = c->getNamespace("float");
  fp->getGenerator("add")->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      // uint exp_bits = args.at("exp_bits")->get<int>();
      // uint frac_bits = args.at("frac_bits")->get<int>();
      // uint ieee_compliance = args.at("ieee_compliance")->get<bool>();
      auto add = def->addInstance(
        "mi",
        "float_CW.add",
        {{"exp_bits", args.at("exp_bits")},
         {"frac_bits", args.at("frac_bits")},
         {"ieee_compliance", Const::make(c, true)}});
      auto io = def->getInterface();
      auto C = Constructor(def);
      def->connect(io->sel("in0"), add->sel("a"));
      def->connect(io->sel("in1"), add->sel("b"));
      def->connect(C.const_(3, 0), add->sel("rnd"));
      def->connect(add->sel("z"), io->sel("out"));
    });

  fp->getGenerator("mul")->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      uint exp_bits = args.at("exp_bits")->get<int>();
      uint frac_bits = args.at("frac_bits")->get<int>();
      ASSERT(frac_bits==7 && exp_bits == 8, "NYI for non bfloat16");
      // uint ieee_compliance = args.at("ieee_compliance")->get<bool>();
      auto mul_hack = def->addInstance(
        "mi",
        "float_CW.mul_hack",
        {{"exp_bits", args.at("exp_bits")},
         {"frac_bits", args.at("frac_bits")},
         {"ieee_compliance", Const::make(c, true)}});
      auto io = def->getInterface();
      auto C = Constructor(def);
      def->connect(io->sel("in0"), mul_hack->sel("a"));
      def->connect(io->sel("in1"), mul_hack->sel("b"));
      def->connect(C.const_(3, 1), mul_hack->sel("rnd"));
      def->connect(mul_hack->sel("z"), io->sel("out"));
    });

  /*
  wire [exp_bits+frac_bits:0] int_out;
  reg sign;
  reg [exp_bits-1:0] exp;
  reg [frac_bits:0] frac;

  CW_fp_mult #(.sig_width(frac_bits+3), .exp_width(exp_bits),
  .ieee_compliance(0)) mul1
  (.a({in0,3'h0}),.b({in1,3'h0}),.rnd('h1),.z({int_out,result_x}),.status());

  always @(*) begin
    sign = int_out[exp_bits+frac_bits];
    exp  = int_out[exp_bits+frac_bits-1:frac_bits];
    frac = {1'b0,int_out[frac_bits-1:0]};
    if ((results_x[2]&(results_x[1] | results_x[0])) | (int_out[0] &
  results_x[2])) begin frac = frac + 1'd1; if (~&exp) begin exp = exp +
  frac[frac_bits]; end end end assign out = {sign, exp, frac[frac_bits-1:0]};
  */

  // Unfinished code translating the above verilog
  /*
    fp->getGenerator("mul")->setGeneratorDefFromFun([](Context* c, Values args,
    ModuleDef* def) { uint exp_bits = args.at("exp_bits")->get<int>(); uint
    frac_bits = args.at("frac_bits")->get<int>(); uint ieee_compliance =
    args.at("ieee_compliance")->get<bool>();

      auto io = def->getInterface();
      if (frac_bits ==7 && exp_bits ==8) { //Special case BFloat16 for now
        auto mul =
    def->addInstance("mi","float_CW",{{"exp_bits",args.at("exp_bits")},{"frac_bits",Const::make(c,10)},{"ieee_compliance",Const::make(c,false)}});
        def->connect(C.concat(C.const_(3,0),io->sel("in0")),mul->sel("a"));
        def->connect(C.concat(C.const_(3,0),io->sel("in1")),mul->sel("b"));
        def->connect(C.const_(3,1),mul->sel("rnd")); //TODO should this be a 1?
        auto result_x = C.slice(mul->sel("z"),0,3);//extra bits
        auto frac0 = C.slice(mul->sel("z"),3,3+7); //frac
        auto exp0 = C.slice(mul->sel("z"),3+7,3+7+8); //exp
        auto sign = mul->sel("z")->sel(16+3-1);
        auto resx0 = result_x->sel(0);
        auto resx1 = result_x->sel(1);
        auto resx2 = result_x->sel(2);

        auto exp0 = C.slice(int_out,7,15)
        frac0 = C.concat(frac0,C.const_(1,0));

        auto round_pred =
    C.or_(C.and_(resx2,C.or_(resx1,resx0)),C.and_(int_out->sel(0),resx2));

        auto frac_true = C.add(frac0,C.const_(7+1,1));
        auto exp_pred = C.not_(C.andr(exp0));
        auto exp_true = C.add(exp,C.frac
        auto out = c.concat(frac
      }
      else if(frac_bits >=10) {
        auto mul =
    def->addInstance("mi","float_CW.mul",{{"exp_bits",args.at("exp_bits")},{"frac_bits",args.at("frac_bits")},{"ieee_compliance",Const::make(c,false)}});

        def->connect(io->sel("in0"),mul->sel("a"));
        def->connect(io->sel("in1"),mul->sel("b"));
        def->connect(C.const_(3,0),mul->sel("rnd"));
        def->connect(mul->sel("z"),io->sel("out"));
      }
      else {
        ASSERT(false,"NYI");
      }
    });
  */
  return fpcw;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(float_CW)
