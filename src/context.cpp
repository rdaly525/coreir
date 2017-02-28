#ifndef CONTEXT_CPP_
#define CONTEXT_CPP_

#include "context.hpp"

using namespace std;

CoreIRContext::CoreIRContext() : err(false), errmsg("") {
  global = new Namespace(this, "_G");
  cache = new TypeCache(this);
}

// Order of this matters
CoreIRContext::~CoreIRContext() {
  delete global;
  for (auto it : libs) delete it.second;
  for (auto it : genargsList) delete it;
  for (auto it : genargList) delete it;
  for (auto it : generatorSet) delete it;
  for (auto it : moduleSet) delete it;
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
Type* CoreIRContext::Flip(Type* t) { return t->getFlipped();}
GenArg* CoreIRContext::GInt(int i) { 
  GenArg* ga = new GenInt(i); 
  genargList.push_back(ga);
  return ga;
}
GenArg* CoreIRContext::GString(string s) { 
  GenArg* ga = new GenString(s); 
  genargList.push_back(ga);
  return ga;
}
GenArg* CoreIRContext::GType(Type* t) { 
  GenArg* ga = new GenType(t); 
  genargList.push_back(ga);
  return ga;
}
int CoreIRContext::toInt(GenArg* g) { return ((GenInt*) g)->i; }
string CoreIRContext::toString(GenArg* g) { return ((GenString*) g)->str; }
Type* CoreIRContext::toType(GenArg* g) { return ((GenType*) g)->t; }

// TODO cache the following for proper memory management
GenArgs* CoreIRContext::newGenArgs(uint len, vector<GenArg*> args) {
  GenArgs* ga = new GenArgs(len, args);
  genargsList.push_back(ga);
  return ga;
}

Generator* CoreIRContext::newGeneratorDecl(string name, ArgKinds kinds, TypeGen* tg) {
  Generator* g = new Generator(this,name,kinds,tg);
  generatorSet.insert(g);
  return g;
}

Module* CoreIRContext::newModuleDecl(string name, Type* t) {
  Module* m = new Module(this,name,t);
  moduleSet.insert(m);
  return m;
}

CoreIRContext* newContext() {
  CoreIRContext* m = new CoreIRContext();
  return m;
}

void deleteContext(CoreIRContext* m) { delete m; }



#endif //CONTEXT_CPP_
