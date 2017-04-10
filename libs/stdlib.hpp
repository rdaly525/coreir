#ifndef STDLIB_HPP_
#define STDLIB_HPP_

#include "context.hpp"

using namespace CoreIR;

Type* binop_type(Context* c, Args args) {
  int n = args.at("width")->arg2Int();
  Type* narray = c->Array(n,c->BitOut());
  return c->Record({
      {"in0",c->Flip(narray)},
      {"in1",c->Flip(narray)},
      {"out",narray}
  });
}

Module* add2(Context* c, Type* t, Args args) {
  int width = args.at("width")->arg2Int();
  Module* m = c->getGlobal()->newModuleDecl("add2_"+to_string(width),t);
  string verilog = "Verilog NYI add2";
  //VModule vm(m);
  //vm.addstmt(VAssign("out","in0 + in1"));
  //m->addVerilog(vm.toString());
  m->addVerilog(verilog);
  return m;
}

Namespace* getStdlib(Context* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
 
  /////////////////////////////////
  // Stdlib Types
  /////////////////////////////////
  Params widthparam = Params({{"width",AINT}});

  //Single bit types
  stdlib->newNamedType("clk","clkIn",c->BitOut());
  stdlib->newNamedType("rst","rstIn",c->BitOut());
  
  //Array types
  TypeGen arrtypegen(
    widthparam,
    [](Context* c, Args args) {
      return c->Array(args.at("width")->arg2Int(),c->BitOut());
    }
  );
 
  stdlib->newNamedType("int","intIn",arrtypegen);
  stdlib->newNamedType("uint","uintIn",arrtypegen);
  
  //Common Function types
  TypeGen boptypegen(
    widthparam,
    [](Context* c, Args args) {
      Type* arr = c->Array(args.at("width")->arg2Int(),c->BitOut());
      return c->Record({{"in0",c->Flip(arr)},{"in1",c->Flip(arr)},{"out",arr}});
    }
  );
  stdlib->newNamedType("binop","binopFlipped",boptypegen);
  
  /////////////////////////////////
  // Stdlib primitives
  /////////////////////////////////
  
  //declare new add2 generator
  Generator* g = stdlib->newGeneratorDecl("add2",widthparam,stdlib->getTypeGen("binop"));
  g->addDef(add2);





  //TODO Hack to get rid of
  Type* binop16 = c->Record({
      {"in0",c->Array(16,c->BitIn())},
      {"in1",c->Array(16,c->BitIn())},
      {"out",c->Array(16,c->BitOut())}
  });
  
  stdlib->newModuleDecl("add2_16",binop16);
  stdlib->newModuleDecl("mult2_16",binop16);
  stdlib->newModuleDecl("const_16",c->Array(16,c->BitOut()),{{"value",AINT}});
  stdlib->newModuleDecl("GPI_16",c->Array(16,c->BitOut()));
  stdlib->newModuleDecl("GPO_16",c->Array(16,c->BitIn()));
  return stdlib;
}

#endif //STDLIB_HPP_
