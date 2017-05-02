#include "coreir-lib/stdlib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(stdlib);


//TODO Maybe also macrofy the name of the c++ function? Not sure

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
  auto arrfun = [](Context* c, Args args) {
    return c->Array(args.at("width")->arg2Int(),c->Bit());
  };
  stdlib->newNominalTypeGen("int","intIn",widthparam,arrfun);
  stdlib->newNominalTypeGen("uint","uintIn",widthparam,arrfun);
  
  //Common Function types
  stdlib->newTypeGen(
    "binop",
    widthparam,
    [](Context* c, Args args) {
      Type* arr = c->Array(args.at("width")->arg2Int(),c->Bit());
      return c->Record({{"in0",c->Flip(arr)},{"in1",c->Flip(arr)},{"out",arr}});
    }
  );
  
  /////////////////////////////////
  // Stdlib primitives
  /////////////////////////////////
  
  //declare new add2 generator
  stdlib->newGeneratorDecl("add2",widthparam,stdlib->getTypeGen("binop"));

  //TODO Hack to get rid of
  Type* binop16 = c->Record({
      {"in0",c->Array(16,c->BitIn())},
      {"in1",c->Array(16,c->BitIn())},
      {"out",c->Array(16,c->Bit())}
  });
  
  Type* outType = c->Record({
    {"out",c->Array(16,c->Bit())}
  });

  Type* inType = c->Record({
    {"in",c->Array(16,c->BitIn())}
  });

  stdlib->newModuleDecl("add2_16",binop16);
  stdlib->newModuleDecl("mult2_16",binop16);
  stdlib->newModuleDecl("const_16",outType,{{"value",AINT}});
  stdlib->newModuleDecl("GPI_16",outType);
  stdlib->newModuleDecl("GPO_16",inType);
  return stdlib;
}
