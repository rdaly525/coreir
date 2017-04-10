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
  
  //Add bop typegen to library
  stdlib->newNamedType("binop","binop_F",TypeGen({{"width",AINT}},binop_type,false));
  
  //declare new add2 generator
  Generator* g = stdlib->newGeneratorDecl("add2",{{"width",AINT}},stdlib->getTypeGen("binop"));
  g->addDef(add2);
  
  //Type* binop16 = binop_type(c,c->genArgs({{"width",c->int2Arg(16)}}),{{"width",AINT}});
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
