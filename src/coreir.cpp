extern "C" {
  #include "coreir.h"
}

#include "context.hpp"

extern "C" {
  C_CoreIRContext* C_newContext() {
    return reinterpret_cast<C_CoreIRContext*>(newContext());
  }
  void C_deleteContext(C_CoreIRContext* c) {
    deleteContext(reinterpret_cast<CoreIRContext*>(c));
  }
}
