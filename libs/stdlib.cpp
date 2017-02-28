#ifndef STDPRIMS_CPP_
#define STDPRIMS_CPP_

#include "stdlib.hpp"
#include "context.hpp"
//#include "verilog.hpp"
//#include "genargs.hpp"

//ModuleDef* binop(Namespace* ns, GenArgs* genargs) {
//  int n = ((GenInt*) ((*genargs)[0]))->i;
//  string opsym = ((GenString*) ((*genargs)[1]))->str;
//  string opname = ((GenString*) ((*genargs)[2]))->str;
//  Type* t = Record({{"in0",Int(n,IN)},{"in1",Int(n,IN)},{"out",Int(n)}});
//  ModuleDef* m = new ModuleDef(opname+"2_"+to_string(n),t);
//  VModule vm(m);
//  vm.addstmt(VAssign("out","in0 "+opsym+" in1"));
//  m->addVerilog(vm.toString());
//  ns->addModuleDef(m);
//  return m;
//}
Type* bop_type(CoreIRContext* c, GenArgs* args, ArgKinds kinds) {
  int n = c->toInt((*args)[0]);
  Type* narray = c->Array(n,c->BitOut());
  return c->Record({
      {"in0",c->Flip(narray)},
      {"in1",c->Flip(narray)},
      {"out",narray}
  });
}
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


Namespace* registerStdlib(CoreIRContext* c) {
  
  Namespace* stdlib = newNamespace("stdlib");
  c->registerLib(stdlib);

  //Add bop typegen to library
  stdlib->newTypeGen("bop","bop_flipped",{GINT},bop_type);
 
  //Create new generator and add definition
  Generator* add2Gen = c->newGeneratorDecl("add2",{GINT},stdlib->getTypeGen("bop"));
  add2Gen->addGeneratorDef(add2);
  
  //Add Generator to library
  stdlib->addGenerator(add2Gen);
  
  return stdlib;
}
#endif //STDPRIMS_CPP_
