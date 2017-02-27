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
void CoreIRContext::registerLib(Namespace* lib) {
  string name = lib->getName();
  if (libs.find(name) != libs.end()) {
    //TODO how do I deal with linking in headers
    cout << "ERROR: added lib twice: " << name << endl;
    exit(0);
  }
  libs.emplace(name,lib);
}



Type* CoreIRContext::Any() { return cache->newAny(); }
Type* CoreIRContext::BitIn() { return cache->newBitIn(); }
Type* CoreIRContext::BitOut() { return cache->newBitOut(); }
Type* CoreIRContext::Array(uint n, Type* t) { return cache->newArray(n,t);}
Type* CoreIRContext::Record(RecordParams rp) { return cache->newRecord(rp); }
Type* CoreIRContext::TypeGenInst(TypeGen* tgd, GenArgs* args) { return cache->newTypeGenInst(tgd,args); }
Type* CoreIRContext::Flip(Type* t) {return t->getFlipped();}
GenArg* CoreIRContext::GInt(int i) { return new GenInt(i); }
GenArg* CoreIRContext::GString(string s) { return new GenString(s); }
GenArg* CoreIRContext::GType(Type* t) { return new GenType(t); } 
int CoreIRContext::toInt(GenArg* g) { return ((GenInt*) g)->i; }
string CoreIRContext::toString(GenArg* g) { return ((GenString*) g)->str; }
Type* CoreIRContext::toType(GenArg* g) { return ((GenType*) g)->t; }

Generator* CoreIRContext::newGeneratorDecl(string name, ArgKinds kinds, TypeGen* tg) {
  return new Generator(this,name,kinds,tg);
}

Module* CoreIRContext::newModuleDecl(string name, Type* t) {
  return new Module(this,name,t);
}


CoreIRContext* newContext() {
  CoreIRContext* m = new CoreIRContext();
  return m;
}

void deleteContext(CoreIRContext* m) { delete m; }



#endif //CONTEXT_CPP_
