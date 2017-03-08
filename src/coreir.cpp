extern "C" {
  #include "coreir.h"
}

#include "context.hpp"
#include "passes.hpp"

template <class T1, class T2>
T1 rcast(T2 in) {
  return reinterpret_cast<T1>(in);
}

extern "C" {
  COREContext* CORENewContext() {
    return rcast<COREContext*>(newContext());
  }
  void COREDeleteContext(COREContext* c) {
    deleteContext(rcast<Context*>(c));
  }
  COREType* COREAny(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->Any());
  }
  COREType* COREBitIn(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->BitIn());
  }
  COREType* COREBitOut(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->BitOut());
  }
  COREType* COREArray(COREContext* c,u32 len, COREType* elemType) {
    return rcast<COREType*>(rcast<Context*>(c)->Array(len,rcast<Type*>(elemType)));
  }
  //COREType* COREArray(u32 len, COREType* elemType); 
  void COREPrintType(COREType* t) {
    rcast<Type*>(t)->print();
  }
  
  COREModule* CORELoadModule(COREContext* c, char* filename) {
    string file(filename);
    return rcast<COREModule*>(loadModule(rcast<Context*>(c),file));
  }

  void COREPrintModule(COREModule* m) {
    rcast<Module*>(m)->print();
  }

}
