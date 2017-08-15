#include "coreirprims.hpp"

//#include "_coreirprims_bitwise.cpp"
//#include "_coreirprims_arithmetic.cpp"
//#include "_coreirprims_state.cpp"
//#include "_coreirprims_convert.cpp"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(coreirprims);

using namespace CoreIR;

void coreirprims_state(Context* c, Namespace* coreirprims) {
  
  //Template
  /* Name: 
   * GenParams: 
   *    <Argname>: <Argtype>, <description>
   * Type: 
   * Fun: 
   * Argchecks: 
   */
   
  /* Name: reg
   * GenParams: 
   *    regType: TYPE, Type of register
   *    en: BOOL, has enable?
   *    clr: BOOL, has clr port
   *    rst: BOOL, has asynchronous reset
   * ConfigParams
   *    resetval: UINT, value at reset
   * Type: {'in':regType
   * Fun: out <= (rst|clr) ? resetval : en ? in : out;
   * Argchecks: 
   */
  auto regFun = [](Context* c, Args args) { 
    uint width = args.at("width")->get<ArgInt>();
    bool en = args.at("en")->get<ArgBool>();
    bool clr = args.at("clr")->get<ArgBool>();
    bool rst = args.at("rst")->get<ArgBool>();
    assert(!(clr && rst));

    RecordParams r({
        {"in",c->BitIn()->Arr(width)},
        {"out",c->Bit()->Arr(width)}
    });
    if (en) r.push_back({"en",c->BitIn()});
    if (clr) r.push_back({"clr",c->BitIn()});
    if (rst) r.push_back({"rst",c->BitIn()});
    return c->Record(r);
  };
  Params regGenParams({
    {"width",AINT},
    {"en",ABOOL},
    {"clr",ABOOL},
    {"rst",ABOOL}
  });
  Params regConfigParams({{"init",AINT}});
  TypeGen* regTypeGen = coreirprims->newTypeGen("regType",regGenParams,regFun);
  auto reg = coreirprims->newGeneratorDecl("reg",regTypeGen,regGenParams,regConfigParams);
  reg->setDefaultGenArgs({{"en",c->argBool(false)},{"clr",c->argBool(false)},{"rst",c->argBool(false)}});
  reg->setDefaultConfigArgs({{"init",c->argInt(0)}});
}

Namespace* CoreIRLoadLibrary_coreirprims(Context* c) {
  
  Namespace* coreirprims = c->newNamespace("coreir");
 
  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparams = Params({{"width",AINT}});

  //Single bit types
  coreirprims->newNamedType("clk","clkIn",c->Bit());
  coreirprims->newNamedType("rst","rstIn",c->Bit());
  
  //Array types
  //coreirprims->newNominalTypeGen("int","intIn",widthparams,arrfun);
  //coreirprims->newNominalTypeGen("uint","uintIn",widthparams,arrfun);
  
  //Common Function types
  coreirprims->newTypeGen(
    "unary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      Type* ptype = c->Bit()->Arr(width);
      if (width==1) ptype = c->Bit();
      return c->Record({
        {"in",c->Flip(ptype)},
        {"out",ptype}
      });
    }
  );
  coreirprims->newTypeGen(
    "binary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      Type* ptype = c->Bit()->Arr(width);
      if (width==1) ptype = c->Bit();
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"out",ptype}
      });
    }
  );
  //TODO should I change the width=1 -> bit for the reduces too?
  coreirprims->newTypeGen(
    "binaryReduce",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      Type* ptype = c->Bit()->Arr(width);
      if (width==1) ptype = c->Bit();
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"out",c->Bit()}
      });
    }
  );
  coreirprims->newTypeGen(
    "unaryReduce",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      Type* ptype = c->Bit()->Arr(width);
      if (width==1) ptype = c->Bit();
      return c->Record({
        {"in",c->Flip(ptype)},
        {"out",ptype}
      });
    }
  );
  
  ////For repeat
  //coreirprims->newTypeGen(
  //  "unaryExpand",
  //  widthparams,
  //  [](Context* c, Args args) {
  //    uint width = args.at("width")->get<ArgInt>();
  //    return c->Record({
  //      {"in",c->BitIn()},
  //      {"out",c->Bit()->Arr(width)}
  //    });
  //  }
  //);
  //For mux
  coreirprims->newTypeGen(
    "ternary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      Type* ptype = c->Bit()->Arr(width);
      if (width==1) ptype = c->Bit();
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"sel",c->BitIn()},
        {"out",ptype}
      });
    }
  );
  
  /////////////////////////////////
  // Stdlib bitwise primitives
  //   not,and,or,xor,andr,orr,xorr,shl,lshr,ashr,dshl,dlshr,dashr
  /////////////////////////////////
  //coreirprims_bitwise(c,coreirprims);

  /////////////////////////////////
  // Stdlib Arithmetic primitives
  //   add,sub,mul,div,lt,leq,gt,geq,eq,neq,neg
  /////////////////////////////////

  //Lazy way:
  
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = coreirprims->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      coreirprims->newGeneratorDecl(op,tg,widthparams);
    }
  }


  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  //TODO 
  //coreirprims_convert(c,coreirprims);
  
  //This defines a passthrough module. It is basically a nop that just passes the signal through
  Params passthroughParams({
    {"type",ATYPE},
  });
  TypeGen* passthroughTG = coreirprims->newTypeGen(
    "passthrough",
    passthroughParams,
    [](Context* c, Args args) {
      Type* t = args.at("type")->get<ArgType>();
      return c->Record({
        {"in",t->getFlipped()},
        {"out",t}
      });
    }
  );
  coreirprims->newGeneratorDecl("passthrough",passthroughTG,passthroughParams);
  

  /////////////////////////////////
  // Stdlib stateful primitives
  //   reg, ram, rom
  /////////////////////////////////
  coreirprims_state(c,coreirprims);
  //Add Const
  coreirprims->newTypeGen(
    "out", 
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
  coreirprims->newGeneratorDecl("const",coreirprims->getTypeGen("out"),widthparams,{{"value",AINT}});
  
  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  //TODO 
  //coreirprims_convert(c,coreirprims);

  return coreirprims;
}
