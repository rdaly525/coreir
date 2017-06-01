#include "coreir-lib/stdlib.h"

//#include "_stdlib_convert.cpp"
//#include "_stdlib_bitwise.cpp"
#include "_stdlib_state.cpp"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(stdlib);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_stdlib(Context* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
 
  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparam = Params({{"width",AINT}});

  //Single bit types
  stdlib->newNamedType("clk","clkIn",c->Bit());
  stdlib->newNamedType("rst","rstIn",c->Bit());
  
  //Array types
  //stdlib->newNominalTypeGen("int","intIn",widthparam,arrfun);
  //stdlib->newNominalTypeGen("uint","uintIn",widthparam,arrfun);
  
  //Common Function types
  stdlib->newTypeGen(
    "binop",
    widthparam,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(2)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

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
  // Stdlib bitwise primitives
  //   not,and,or,xor,andr,orr,xorr,shift
  /////////////////////////////////
  //TODO
  //stdlib_bitwise(c,stdlib);

  /////////////////////////////////
  // Stdlib Arithmetic primitives
  //   dshift,add,sub,mul,div,lt,leq,gt,geq,eq,neq,neg
  /////////////////////////////////
  stdlib->newGeneratorDecl("add",stdlib->getTypeGen("binop"),widthparam);
  stdlib->newGeneratorDecl("mul",stdlib->getTypeGen("binop"),widthparam);


  /////////////////////////////////
  // Stdlib stateful primitives
  //   reg, ram, rom
  /////////////////////////////////
  stdlib_state(c,stdlib);


  //Add Const
  stdlib->newTypeGen(
    "out", 
    widthparam,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
  stdlib->newGeneratorDecl("const",stdlib->getTypeGen("out"),widthparam,{{"value",AINT}});

  return stdlib;
}
