#ifndef STDLIB_HPP_
#define STDLIB_HPP_

#include "context.hpp"

Type* binop_type(Context* c, GenArgs* args, GenParams kinds) {
  int n = c->toInt((*args)["w"]);
  Type* narray = c->Array(n,c->BitOut());
  return c->Record({
      {"in0",c->Flip(narray)},
      {"in1",c->Flip(narray)},
      {"out",narray}
  });
}

Module* add2(Context* c, Type* t, GenArgs* args, GenParams argkinds) {
  int n = c->toInt((*args)["w"]);
  Module* m = c->getGlobal()->newModuleDecl("add2_"+to_string(n),t);
  string verilog = "Verilog NYI add2";
  //VModule vm(m);
  //vm.addstmt(VAssign("out","in0 + in1"));
  //m->addVerilog(vm.toString());
  m->addVerilog(verilog);
  return m;
}

Namespace* getStdlib(Context* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
  //c->registerLib(stdlib);
  //Add bop typegen to library
  stdlib->newTypeGen("binop","binop_F",{{"w",GINT}},binop_type);
  
  //declare new add2 generator
  Generator* g = stdlib->newGeneratorDecl("add2",{{"w",GINT}},stdlib->getTypeGen("binop"));
  g->addDef(add2);
  
  Type* binop16 = binop_type(c,c->newGenArgs({{"w",c->GInt(16)}}),{{"w",GINT}});
  stdlib->newModuleDecl("add2_16",binop16);
  stdlib->newModuleDecl("mult2_16",binop16);
  stdlib->newModuleDecl("const_16",c->Array(16,c->BitOut()),{{"value",GINT}});
  stdlib->newModuleDecl("GPI_16",c->Array(16,c->BitOut()));
  stdlib->newModuleDecl("GPO_16",c->Array(16,c->BitIn()));
  return stdlib;
}

#endif //STDLIB_HPP_
