#ifndef STDLIB_HPP_
#define STDLIB_HPP_

#include "context.hpp"

//#include "stdlib_defaults.hpp"

using namespace CoreIR;

Namespace* getStdlib(Context* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
 
  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparam = Params({{"width",AINT}});

  /*
  //Single bit types
  stdlib->newNamedType("clk","clkIn",c->BitOut());
  stdlib->newNamedType("rst","rstIn",c->BitOut());
  
  //Array types
  auto arrfun = [](Context* c, Args args) {
    return c->Array(args.at("width")->arg2Int(),c->BitOut());
  };
  stdlib->newNominalTypeGen("int","intIn",widthparam,arrfun);
  stdlib->newNominalTypeGen("uint","uintIn",widthparam,arrfun);
  
  */
  //Common Function types
  stdlib->newTypeGen(
    "binop",
    widthparam,
    [](Context* c, Args args) {
      Type* arr = c->Array(args.at("width")->arg2Int(),c->BitOut());
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
      {"out",c->Array(16,c->BitOut())}
  });
  
  Type* outType = c->Record({
    {"out",c->Array(16,c->BitOut())}
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

#endif //STDLIB_HPP_
