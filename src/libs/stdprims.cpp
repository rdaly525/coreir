#ifndef STDPRIMS_CPP_
#define STDPRIMS_CPP_

#include "stdprims.hpp"
#include "coreir.hpp"



//in0:Uint(N),in1:Uint(N),out:Uint(N)
template <typename T>
void updateOutput_add2(void* iface,void* state,void* dirty,Genargs* genargs) {
  void** dirtyCast = (void**) dirty;
  dirty_t* in0_d = (dirty_t*) (dirtyCast[0]);
  dirty_t* in1_d = (dirty_t*) (dirtyCast[1]);
  dirty_t* out_d = (dirty_t*) (dirtyCast[2]);
  if (isDirty(in0_d) || isDirty(in1_d) ) {
    void** ifaceCast = (void**) iface;
    T* in0 = (T*) (ifaceCast[0]);
    T* in1 = (T*) (ifaceCast[1]);
    T* out = (T*) (ifaceCast[2]);
    *out = *in0 + *in1;
    setDirty(out_d);
  }
}

ModuleDef* stdprim_add2(NameSpace* ns, Genargs* genargs) {
  uint32_t n = *((uint32_t*) genargs->data);
  simfunctions_t s;
  s.allocateState = NULL;
  if (n <= 8) s.updateOutput = updateOutput_add2<uint8_t> ;
  else if (n <= 16) s.updateOutput = updateOutput_add2<uint16_t> ;
  else if (n <= 32) s.updateOutput = updateOutput_add2<uint32_t> ;
  else if (n <= 64) s.updateOutput = updateOutput_add2<uint64_t> ;
  else {
    exit(0);
    throw "FUCK";
  }
  string verilog = "VERILOG_PLUS";//createVerilogBinOp("+",n)
  Type* t = Record({{"in0",Int(n,IN)},{"in1",Int(n,IN)},{"out",Int(n)}});
  ModuleDef* m = new ModuleDef("add2_"+to_string(n),t);
  m->addVerilog(verilog);
  m->addSimfunctions(s);
  ns->addModuleDef(m);
  return m;
}

NameSpace* registerStdPrims(CoreIRContext* c, string nameSpace) {
  NameSpace* l = c->registerLib(nameSpace);
  GeneratorDef* genDef = new GeneratorDef("add2",stdprim_add2);
  l->addGeneratorDef(genDef);
  Genargs* g= new Genargs(Int(32));
  uint32_t* n16 = (uint32_t*) (g->data);
  *n16 = 16;
  l->addModuleDef(stdprim_add2(l,g));
  delete g;
  
  return l;
}

#endif //STDPRIMS_CPP_
