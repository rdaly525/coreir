#include "stdlib.hpp"

//#include "_stdlib_bitwise.cpp"
//#include "_stdlib_arithmetic.cpp"
#include "_stdlib_state.cpp"
//#include "_stdlib_convert.cpp"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(stdlib);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_stdlib(Context* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
 
  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparams = Params({{"width",AINT}});

  //Single bit types
  stdlib->newNamedType("clk","clkIn",c->Bit());
  stdlib->newNamedType("rst","rstIn",c->Bit());
  
  //Array types
  //stdlib->newNominalTypeGen("int","intIn",widthparams,arrfun);
  //stdlib->newNominalTypeGen("uint","uintIn",widthparams,arrfun);
  
  //Common Function types
  stdlib->newTypeGen(
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
  stdlib->newTypeGen(
    "binary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      Type* ptype = c->Bit()->Arr(width);
      if (width==1) ptype = c->Bit();
      return c->Record({
        {"in",c->Flip(ptype)->Arr(2)},
        {"out",ptype}
      });
    }
  );
  //TODO should I change the width=1 -> bit for the reduces too?
  stdlib->newTypeGen(
    "binaryReduce",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(2)},
        {"out",c->Bit()}
      });
    }
  );
  stdlib->newTypeGen(
    "unaryReduce",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)},
        {"out",c->Bit()}
      });
    }
  );
  //For repeat
  stdlib->newTypeGen(
    "unaryExpand",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
  //For mux
  stdlib->newTypeGen(
    "ternary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      Type* ptype = c->Bit()->Arr(width);
      if (width==1) ptype = c->Bit();
      return c->Record({
        {"in",c->Flip(ptype)},
        {"sel",c->BitIn()},
        {"out",ptype}
      });
    }
  );
  
  /////////////////////////////////
  // Stdlib bitwise primitives
  //   not,and,or,xor,andr,orr,xorr,shl,lshr,ashr,dshl,dlshr,dashr
  /////////////////////////////////
  //stdlib_bitwise(c,stdlib);

  /////////////////////////////////
  // Stdlib Arithmetic primitives
  //   add,sub,mul,div,lt,leq,gt,geq,eq,neq,neg
  /////////////////////////////////

  //Lazy way:
  
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = stdlib->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      stdlib->newGeneratorDecl(op,tg,widthparams);
    }
  }


  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  //TODO 
  //stdlib_convert(c,stdlib);
  
  //This defines a passthrough module. It is basically a nop that just passes the signal through
  Params passthroughParams({
    {"type",ATYPE},
  });
  TypeGen* passthroughTG = stdlib->newTypeGen(
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
  stdlib->newGeneratorDecl("passthrough",passthroughTG,passthroughParams);
  

  /////////////////////////////////
  // Stdlib stateful primitives
  //   reg, ram, rom
  /////////////////////////////////
  stdlib_state(c,stdlib);
  //Add Const
  stdlib->newTypeGen(
    "out", 
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
  stdlib->newGeneratorDecl("const",stdlib->getTypeGen("out"),widthparams,{{"value",AINT}});
  
  /////////////////////////////////
  // Stdlib convert primitives
  //   slice,concat,cast,strip
  /////////////////////////////////
  //TODO 
  //stdlib_convert(c,stdlib);

  return stdlib;
}
