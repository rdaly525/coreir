#ifndef STDLIB_V1_HPP_
#define STDLIB_V1_HPP_

#include "context.hpp"

//Type boptype
Module* add2(Context* c, Type* t, GenArgs* args, ArgKinds argkinds) {
  int n = c->toInt((*args)["w"]);
  Module* m = c->getGlobal()->newModuleDecl("add2_"+to_string(n),t);
  string verilog = "NYI add2";
  //VModule vm(m);
  //vm.addstmt(VAssign("out","in0 + in1"));
  //m->addVerilog(vm.toString());
  m->addVerilog(verilog);
  return m;
}


Namespace* getStdlib_v1(Context* c) {
  
  //Get the stdlib header which contains all the types
  Namespace* stdlib = c->getNamespace("stdlib");
  
  Namespace* stdlib_v1 = c->newNamespace("stdlib_v1");

  //Create new generator and add definition
  Generator* add2Gen = stdlib_v1->newGeneratorDecl("add2",{{"w",GINT}},stdlib->getTypeGen("binop"));
  add2Gen->addDef(add2);
  
  return stdlib_v1;
}
#endif //STDLIB_V1_HPP_
