#include "coreirprims.hpp"

//#include "_coreirprims_bitwise.cpp"
//#include "_coreirprims_arithmetic.cpp"
//#include "_coreirprims_state.cpp"
//#include "_coreirprims_convert.cpp"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(coreirprims);

using namespace CoreIR;

void coreirprims_convert(Context* c, Namespace* coreirprims) {


  /* Name: slice
   * GenParams: 
   *    lo: UINT, The start index of the slice
   *    hi: UINT, The stop index of the slice non-inclusive
   *    arrtype: TYPE, the array type of the input.
   * Type: In(arrtype) -> Out(arrtype.elemtype)[hi-lo+1]
   * Fun: out = in[lo:hi]
   * Argchecks: 
   *    arrtype.isKind(ARRAY)
   *    start < stop <= arrtype.len
   */
  Params sliceParams({
    {"width",AINT},
    {"lo",AINT},
    {"hi",AINT}
  });
  auto sliceTypeGen = coreirprims->newTypeGen(
    "sliceTypeFun",
    sliceParams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      uint lo = args.at("lo")->get<ArgInt>();
      uint hi = args.at("hi")->get<ArgInt>();
      ASSERT(lo < hi && hi<=width,"Bad slice args!");
      return c->Record({
        {"in",c->BitIn()->Arr(width)},
        {"out",c->Bit()->Arr(hi-lo)}
      });
    }
  );
  auto slice = coreirprims->newGeneratorDecl("slice",sliceTypeGen,sliceParams);
  json jverilog;
  jverilog["parameters"] = {"width","lo","hi"};
  slice->getMetaData()["verilog"] = jverilog;

  /* Name: concat
   * GenParams: 
   *    larrtype: TYPE, the left array
   *    rarrtype: TYPE, the right array
   * Type: In(larrtype) -> In(rarrtype) -> Out(larrtype.elemtype)[larrtype.len+rarrtype.len]
   * Fun: out = concat(in[0],in[1])
   * Argchecks: 
   *    larrtype.isKind(ARRAY)
   *    rarrtype.isKind(ARRAY)
   *    larrtype.elemtype == rarrtype.elemtype
   */
  Params concatParams({
    {"lwidth",AINT},
    {"rwidth",AINT}
  });
  auto concatTypeGen = coreirprims->newTypeGen(
    "concatTypeFun",
    concatParams,
    [](Context* c, Args args) {
      uint lwidth = args.at("lwidth")->get<ArgInt>();
      uint rwidth = args.at("rwidth")->get<ArgInt>();
      return c->Record({
        {"inl",c->BitIn()->Arr(lwidth)},
        {"inr",c->BitIn()->Arr(rwidth)},
        {"out",c->Bit()->Arr(lwidth+rwidth)}
      });
    }
  );
  auto concat = coreirprims->newGeneratorDecl("concat",concatTypeGen,concatParams);
  jverilog["parameters"] = {"lwidth","rwidth"};
  concat->getMetaData()["verilog"] = jverilog;

  /* Name: strip
   * GenParams: 
   *    namedtype: TYPE, the type you want to strip
   * Type: namedtype -> namedtype.raw
   * Fun: out = in
   * Argchecks: 
   *    namedtype.isKind(NAMED)
   */
  //Params stripParams({
  //  {"namedtype",TYPE}
  //});
  //auto stripFun = [](Context* c, Args args) { return c->Any(); } //TODO
  //TypeGen stripTypeGen(stripParams,stripFun);
  //stdlib->newGeneratorDecl("strip",stripParams,stripTypeGen);

  /* Name: cast
   * GenParams: 
   *    intype: TYPE, precast type
   *    outtype: TYPE, postcast type
   * Type: intype -> outype
   * Fun: out = (outtype) in
   * Argchecks: 
   *    intype.structure == outtype.structure
   */
  //Params castParams({
  //  {"intype",TYPE},
  //  {"outtype",TYPE}
  //});
  //auto castFun = [](Context* c, Args args) { return c->Any(); } //TODO
  //TypeGen castTypeGen(castParams,castFun);
  //stdlib->newGeneratorDecl("cast",castParams,castTypeGen);

}

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
        {"in" , c->BitIn()->Arr(width)},
        {"clk", c->Named("coreir", "clkIn")},
        {"out", c->Bit()->Arr(width)}
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
  
  json jverilog;
  jverilog["parameters"] = {"width","init"};
  reg->getMetaData()["verilog"] = jverilog;

  //Set nameGen function
  auto regNameGen = [](Args args) {
    string name = "reg_P";
    bool rst = args["rst"]->get<ArgBool>();
    bool clr = args["clr"]->get<ArgBool>();
    bool en = args["en"]->get<ArgBool>();
    if (rst) name += "R";
    if (clr) name += "C";
    if (en) name += "E";
    return name;
  };
  reg->setNameGen(regNameGen);

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
        {"out",c->Bit()}
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


  json jverilog;
  jverilog["parameters"] = {"width"};
  //Lazy way:
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = coreirprims->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      Generator* g = coreirprims->newGeneratorDecl(op,tg,widthparams);
      g->getMetaData()["verilog"] = jverilog;
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
  auto Const = coreirprims->newGeneratorDecl("const",coreirprims->getTypeGen("out"),widthparams,{{"value",AINT}});
  jverilog["parameters"] = {"width","value"};
  Const->getMetaData()["verilog"] = jverilog;

  //Add Term
  coreirprims->newTypeGen(
    "in", 
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)}
      });
    }
  );
  coreirprims->newGeneratorDecl("term",coreirprims->getTypeGen("in"),widthparams);

  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  coreirprims_convert(c,coreirprims);

  return coreirprims;
}
