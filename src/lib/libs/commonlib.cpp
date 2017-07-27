#include "coreir-lib/commonlib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(commonlib);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_commonlib(Context* c) {
  
  Namespace* commonlib = c->newNamespace("commonlib");
 
  /////////////////////////////////
  // Commonlib Types
  /////////////////////////////////
  Params widthparams = Params({{"width",AINT}});

  //Single bit types
  commonlib->newNamedType("clk","clkIn",c->Bit());
  commonlib->newNamedType("rst","rstIn",c->Bit());
  
  //Common Function types
  commonlib->newTypeGen(
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
  commonlib->newTypeGen(
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
  commonlib->newTypeGen(
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
  commonlib->newTypeGen(
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
  commonlib->newTypeGen(
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
  commonlib->newTypeGen(
    "ternary",
    widthparams,
    [](Context* c, Args args) {
      uint width = args.at("width")->get<ArgInt>();
      return c->Record({
        {"in",c->Record({
          {"data",c->BitIn()->Arr(width)->Arr(2)},
          {"bit",c->BitIn()}
        })},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );
  
  /////////////////////////////////
  // Commonlib bitwise primitives
  //   
  /////////////////////////////////
  //commonlib_bitwise(c,commonlib);

  /////////////////////////////////
  // Commonlib Arithmetic primitives
  //   umin,smin,umax,smax
  /////////////////////////////////

  //Lazy way:
  unordered_map<string,vector<string>> opmap({
    {"unary",{}},
    {"unaryReduce",{}},
    {"binary",{
     "umin","smin","umax","smax"
    }},
    {"binaryReduce",{
    }},
    {"ternary",{}},
  });
  
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = commonlib->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      commonlib->newGeneratorDecl(op,tg,widthparams);
    }
  }

  return commonlib;
}
