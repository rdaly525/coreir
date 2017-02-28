#ifndef STDLIB_V1_HPP_
#define STDLIB_V1_HPP_

#include "context.hpp"

//Type boptype
Module* add2(CoreIRContext* c, Type* t, GenArgs* args, ArgKinds argkinds) {
  int n = c->toInt((*args)[0]);
  Module* m = c->newModuleDecl("add2_"+to_string(n),t);
  string verilog = "NYI add2";
  //VModule vm(m);
  //vm.addstmt(VAssign("out","in0 + in1"));
  //m->addVerilog(vm.toString());
  m->addVerilog(verilog);
  return m;
}


Namespace* getStdlib_v1(CoreIRContext* c) {
  
  //Get the stdlib header which contains all the types
  Namespace* stdlib = c->getNamespace("stdlib");
  
  Namespace* stdlib_v1 = c->newNamespace("stdlib_v1");

  //Create new generator and add definition
  Generator* add2Gen = c->newGeneratorDecl("add2",{GINT},stdlib->getTypeGen("binop"));
  add2Gen->addGeneratorDef(add2);
  
  //Add Generator to library
  stdlib_v1->addGenerator(add2Gen);
  
  return stdlib_v1;
}
#endif //STDLIB_V1_HPP_
