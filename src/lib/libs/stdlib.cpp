#include "coreir-lib/stdlib.h"

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
    "binary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(2)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
  stdlib->newTypeGen(
    "unary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
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
      return c->Record({
        {"in",c->Record({
          {"data",c->BitIn()->Arr(width)},
          {"bit",c->BitIn()}
        })},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

  //Lazy way:
  unordered_map<string,vector<string>> opmap({
    {"unary",{"not","neg"}},
    {"unaryReduce",{"andr","orr","xorr"}},
    {"binary",{
      "and","or","xor",
      "dshl","dlshr","dashr",
      "add","sub","mul",
      "udiv","urem",
      "sdiv","srem","smod"
    }},
    {"binaryReduce",{"eq",
      "slt","sgt","sle","sge",
      "ult","ugt","ule","uge"
    }},
    {"ternary",{"mux"}},
  });
  
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = stdlib->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      stdlib->newGeneratorDecl(op,tg,widthparams);
    }
  }



  /////////////////////////////////
  // Stdlib bitwise primitives
  //   not,and,or,xor,andr,orr,xorr,shl,lshr,ashr,dshl,dlshr,dashr
  /////////////////////////////////
  //stdlib_bitwise(c,stdlib);

  /////////////////////////////////
  // Stdlib Arithmetic primitives
  //   add,sub,mul,div,lt,leq,gt,geq,eq,neq,neg
  /////////////////////////////////

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
