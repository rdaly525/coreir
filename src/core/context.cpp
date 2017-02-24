#ifndef CONTEXT_CPP_
#define CONTEXT_CPP_

#include "context.hpp"

CoreIRContext::CoreIRContext() {
  global = new Namespace("_G");
  cache = new TypeCache(this);
}
CoreIRContext::~CoreIRContext() {
  delete global;
  for (auto it : libs) delete it.second;
  delete cache;
}
Type* CoreIRContext::Any() { return cache->newAny(); }
Type* CoreIRContext::BitIn() { return cache->newBitIn(); }
Type* CoreIRContext::BitOut() { return cache->newBitOut(); }
Type* CoreIRContext::Array(uint n, Type* t) { return cache->newArray(n,t);}
Type* CoreIRContext::Record(RecordParams rp) { return cache->newRecord(rp); }
Type* CoreIRContext::TypeGenInst(TypeGen* tgd, GenArgs* args) { return cache->newTypeGenInst(tgd,args); }

CoreIRContext* newContext() {
  CoreIRContext* m = new CoreIRContext();
  return m;
}

void deleteContext(CoreIRContext* m) { delete m; }



#endif //CONTEXT_CPP_
