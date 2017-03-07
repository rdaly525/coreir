#ifndef CONTEXT_CPP_
#define CONTEXT_CPP_

#include "context.hpp"

using namespace std;

CoreIRContext::CoreIRContext() : maxErrors(3) {
  global = newNamespace("_G");
  cache = new TypeCache(this);
}

// Order of this matters
CoreIRContext::~CoreIRContext() {
  
  for (auto it : namespaceList) delete it;
  for (auto it : genargsList) delete it;
  for (auto it : genargList) delete it;
  for (auto it : generatorList) delete it;
  for (auto it : moduleList) delete it;
  delete cache;
}

bool CoreIRContext::registerLib(Namespace* lib) {
  string name = lib->getName();
  if (libs.find(name) != libs.end()) {
    Error e;
    e.message("Namespace already exists!");
    e.message("  Namespace: " + name);
    error(e);
    return true;
  }
  libs.emplace(name,lib);
  return false;
}

Namespace* CoreIRContext::newNamespace(string name) { 
  Namespace* n = new Namespace(this,name);
  namespaceList.push_back(n);
  return n;
}

Namespace* CoreIRContext::getNamespace(string name) {
  auto it = libs.find(name);
  if (it == libs.end()) {
    Error e;
    e.message("Could Not Find Namespace");
    e.message("  Namespace : " + name);
    e.fatal();
    error(e);
    return nullptr;
  }
  return it->second;
}

// This tries to link all the definitions of def namespace to declarations of decl namespace
// This will clobber declns
bool CoreIRContext::linkLib(Namespace* defns, Namespace* declns) {
  if (haserror()) {
    return true;
  }
  for (auto it : defns->getGenerators()) {
    Generator* gdef = (it.second);
    string gdefname = gdef->getName();
    assert(it.first == gdefname);
    genFun gdeffun = gdef->getDef();
    Generator* gdecl = declns->getGenerator(gdefname);
    
    //If def is not found in decl,
    //  make e.message?
    if (haserror() ) return true;
    
    genFun gdeclfun = gdecl->getDef();

    //case def is found in decl, but def is a decl
    //  Do nothing? Warning? Add it?
    if (!gdeffun) continue;
    
    //case def is found in decl, but decl already has a def
    //  Error, two definitiosn for linking
    if (gdeffun && gdeclfun && (gdeffun != gdeclfun) ) {
      Error e;
      e.message("Cannot link a def if there is already a def! (duplicate symbol)");
      e.message("  Cannot link : " + defns->getName() + "." + gdefname);
      e.message("  To : " + declns->getName() + "." + gdefname);
      error(e);
      return true;
    }

    assert(gdeffun && !gdeclfun); // Internal check
    //case def is found in decl, decl has no def
    //  Perfect, Add def to decl
    gdecl->addDef(gdeffun);
  }

  //TODO do modules as well
  return false;
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
GenArgs* CoreIRContext::newGenArgs(unordered_map<string,GenArg*> args) {
  GenArgs* ga = new GenArgs(this,args);
  genargsList.push_back(ga);
  return ga;
}

Generator* CoreIRContext::newGeneratorDecl(string name, ArgKinds kinds, TypeGen* tg) {
  Generator* g = new Generator(this,name,kinds,tg);
  generatorList.push_back(g);
  return g;
}

Module* CoreIRContext::newModuleDecl(string name, Type* t) {
  Module* m = new Module(this,name,t);
  moduleList.push_back(m);
  return m;
}

CoreIRContext* newContext() {
  CoreIRContext* m = new CoreIRContext();
  return m;
}

void deleteContext(CoreIRContext* m) { 
  cout << "DELETING!" << endl;
  delete m;
}



#endif //CONTEXT_CPP_
