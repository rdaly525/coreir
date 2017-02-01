#ifndef STDPRIMS_CPP_
#define STDPRIMS_CPP_

#include "stdprims.hpp"
#include "coreir.hpp"
#include "verilog.hpp"
#include "genargs.hpp"

ModuleDef* binop(NameSpace* ns, GenArgs* genargs) {
  uint32_t n = ((GenInt*) ((*genargs)[0]))->i;
  string opsym = ((GenString*) ((*genargs)[1]))->str;
  string opname = ((GenString*) ((*genargs)[2]))->str;
  Type* t = Record({{"in0",Int(n,IN)},{"in1",Int(n,IN)},{"out",Int(n)}});
  ModuleDef* m = new ModuleDef(opname+"2_"+to_string(n),t);
  VModule vm(m);
  vm.addstmt(VAssign("out","in0 "+opsym+" in1"));
  m->addVerilog(vm.toString());
  ns->addModuleDef(m);
  return m;
}

ModuleDef* add2(NameSpace* ns, GenArgs* genargs) {
  uint32_t n = ((GenInt*) ((*genargs)[0]))->i;
  
  Type* t = Record({{"in0",Int(n,IN)},{"in1",Int(n,IN)},{"out",Int(n)}});
  ModuleDef* m = new ModuleDef("add2_"+to_string(n),t);
  VModule vm(m);
  vm.addstmt(VAssign("out","in0 + in1"));
  m->addVerilog(vm.toString());
  ns->addModuleDef(m);
  return m;
}


NameSpace* registerStdPrims(CoreIRContext* c, string nameSpace) {
  NameSpace* l = c->registerLib(nameSpace);
  l->addModuleGenDef(new ModuleGenDef("add2",genargs_t({GINT}),add2));
  l->addModuleGenDef(new ModuleGenDef("binop",genargs_t({GINT,GSTRING,GSTRING}),binop));
  
  
  int n = 32;
  GenArgs* g = new GenArgs({GINT},{&n});
  l->addModuleDef(add2(l,g));
  delete g;
  
  return l;
}

NameSpace* registerStdPrims(CoreIRContext* c) {
  return registerStdPrims(c,"stdprims");
}
#endif //STDPRIMS_CPP_
