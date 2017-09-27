#include "coreir/ir/context.h"
#include "coreir/ir/typecache.h"
#include "coreir/ir/passmanager.h"


using namespace std;



namespace CoreIR {

#include "coreirprims.hpp"

Context::Context() : maxErrors(8) {
  global = newNamespace("global");
  cache = new TypeCache(this);
  //Automatically load coreir //defined in coreirprims.h
  CoreIRLoadLibrary_coreirprims(this);
  pm = new PassManager(this);
}

// Order of this matters
Context::~Context() {
  
  //for (auto it : genargsList) delete it;
  for (auto it : recordParamsList) delete it;
  for (auto it : paramsList) delete it;
  for (auto it : namespaces) delete it.second;
  for (auto it : connectionPtrArrays) free(it);
  for (auto it : connectionArrays) free(it);
  for (auto it : wireableArrays) free(it);
  for (auto it : constStringArrays) free(it);
  for (auto it : stringArrays) free(it);
  for (auto it : stringBuffers) free(it);
  for (auto it : directedConnectionPtrArrays) free(it);
  for (auto it : directedInstancePtrArrays) free(it);
  for (auto it : argPtrArrays) free(it);

  delete cache;
}

void Context::print() {
  cout << "Context: " << endl;
  for (auto ns : getNamespaces()) {
    ns.second->print();
  }
  cout << "EndContext" << endl;
}

void Context::error(Error& e) { 
  errors.push_back(e.msg);
  if (e.isfatal || errors.size() >= maxErrors) die();
}
void Context::printerrors() { 
  for (auto err : errors) cout << "ERROR: " << err << endl << endl;
}

void Context::die() {
  printerrors();
  cout << "I AM DYING!" << endl;
  delete this; // sketch but okay if exits I guess
  exit(1);
}


Namespace* Context::newNamespace(string name) { 
  Namespace* n = new Namespace(this,name);
  namespaces.emplace(name,n);
  return n;
}

Namespace* Context::getNamespace(string name) {
  auto it = namespaces.find(name);
  if (it == namespaces.end()) {
    Error e;
    e.message("Could Not Find Namespace");
    e.message("  Namespace : " + name);
    e.fatal();
    error(e);
    return nullptr;
  }
  return it->second;
}

Module* Context::getModule(string ref) {
  vector<string> refsplit = splitRef(ref);
  ASSERT(hasNamespace(refsplit[0]),"Missing namespace: " + refsplit[0]);
  Namespace* ns = getNamespace(refsplit[0]);
  ASSERT(ns->hasModule(refsplit[1]),"Missing module: " + ref);
  return ns->getModule(refsplit[1]);
}

Generator* Context::getGenerator(string ref) {
  vector<string> refsplit = splitRef(ref);
  ASSERT(hasNamespace(refsplit[0]),"Missing namespace: " + refsplit[0]);
  Namespace* ns = getNamespace(refsplit[0]);
  ASSERT(ns->hasGenerator(refsplit[1]),"Missing module: " + ref);
  return ns->getGenerator(refsplit[1]);
}

Instantiable* Context::getInstantiable(string ref) {
  vector<string> refsplit = splitRef(ref);
  ASSERT(hasNamespace(refsplit[0]),"Missing namespace: " + refsplit[0]);
  Namespace* ns = getNamespace(refsplit[0]);
  ASSERT(ns->hasInstantiable(refsplit[1]),"Missing Instantiable: " + ref);
  return ns->getInstantiable(refsplit[1]);
}

void Context::addPass(Pass* p) {
  assert(pm);
  p->addPassManager(pm);
  pm->addPass(p);
}

bool Context::runPasses(vector<string> order, vector<string> namespaces) {
  assert(pm);
  return pm->run(order,namespaces);
}
/* TODO This is not even used in the repo yet. Should write a test for it
// This tries to link all the definitions of def namespace to declarations of decl namespace
// This will clobber declns
bool Context::linkLib(Namespace* nsFrom, Namespace* nsTo) {
  if (haserror()) {
    return true;
  }
  for (auto it : defns->getGenerators()) {
    Generator* gdef = (it.second);
    string gdefname = gdef->getName();
    assert(it.first == gdefname);
    GeneratorDef* gdef = gdef->getDef();
    Generator* gdecl = declns->getGenerator(gdefname);
    
    //If def is not found in decl,
    //  make e.message?
    if (haserror() ) return true;
    
    ModuleDefGenFun gdeclfun = gdecl->getDef();

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
*/

Type* Context::Bit() { return cache->newBit(); }
Type* Context::BitIn() { return cache->newBitIn(); }
Type* Context::Array(uint n, Type* t) { return cache->newArray(n,t);}
Type* Context::Record(RecordParams rp) { return cache->newRecord(rp); }
Type* Context::Named(string nameref) {
  vector<string> split = splitRef(nameref);
  ASSERT(this->hasNamespace(split[0]),"Missing Namespace + " + split[0]);
  ASSERT(this->getNamespace(split[0])->hasNamedType(split[1]),"Missing Named type + " + nameref);
  return this->getNamespace(split[0])->getNamedType(split[1]);
}

Type* Context::Named(string nameref,Args args) {
  vector<string> split = splitRef(nameref);
  ASSERT(this->hasNamespace(split[0]),"Missing Namespace + " + split[0]);
  ASSERT(this->getNamespace(split[0])->hasNamedType(split[1]),"Missing Named type + " + nameref);
  return this->getNamespace(split[0])->getNamedType(split[1],args);
}

Type* Context::Flip(Type* t) { return t->getFlipped();}

Type* Context::In(Type* t) {
  assert(0 && "TODO NYI");
}

Type* Context::Out(Type* t) {
  assert(0 && "TODO NYI");
}

void Context::setTop(Module* top) {
  ASSERT(top && top->hasDef(), top->toString() + " has no def!");
  this->top = top;
}
void Context::setTop(string topRef) {
  auto topsplit = splitString<vector<string>>(topRef,'.');
  ASSERT(topsplit.size()==2,topRef + " is not a valid top!");
  ASSERT(this->hasNamespace(topsplit[0]),"Missing namespace " + topsplit[0]);
  Namespace* topns = this->getNamespace(topsplit[0]);
  ASSERT(topns->hasModule(topsplit[1]),"Missing module " + topRef);
  this->top = topns->getModule(topsplit[1]);
  ASSERT(this->top->hasDef(),topRef + " has no def!");
}


TypeGen* Context::getTypeGen(string nameref) {
  vector<string> split = splitRef(nameref);
  ASSERT(this->hasNamespace(split[0]),"Missing Namespace + " + split[0]);
  ASSERT(this->getNamespace(split[0])->hasTypeGen(split[1]),"Missing TypeGen + " + nameref);
  return this->getNamespace(split[0])->getTypeGen(split[1]);
}

RecordParams* Context::newRecordParams() {
  RecordParams* record_param = new RecordParams();
  recordParamsList.push_back(record_param);
  return record_param;
}

Params* Context::newParams() {
  Params* params = new Params();
  paramsList.push_back(params);
  return params;
}

Args* Context::newArgs() {
  Args* args = new Args();
  argsList.push_back(args);
  return args;
}

Arg** Context::newArgPtrArray(int size) {
    Arg** arr = (Arg**) malloc(sizeof(Arg*) * size);
    argPtrArrays.push_back(arr);
    return arr;
}

Connection* Context::newConnectionArray(int size) {
  Connection* arr = (Connection*) malloc(sizeof(Connection) * size);
  connectionArrays.push_back(arr);
  return arr;
}

Connection** Context::newConnectionPtrArray(int size) {
  Connection** arr = (Connection**) malloc(sizeof(Connection*) * size);
  connectionPtrArrays.push_back(arr);
  return arr;
}

const char** Context::newConstStringArray(int size) {
    const char** arr = (const char**) malloc(sizeof(const char*) * size);
    constStringArrays.push_back(arr);
    return arr;
}

char** Context::newStringArray(int size) {
    char** arr = (char**) malloc(sizeof(char*) * size);
    stringArrays.push_back(arr);
    return arr;
}

char* Context::newStringBuffer(int size) {
    char* arr = (char*) malloc(sizeof(char) * size);
    stringBuffers.push_back(arr);
    return arr;
}

Wireable** Context::newWireableArray(int size) {
  Wireable** arr = (Wireable**) malloc(sizeof(Wireable*) * size);
  wireableArrays.push_back(arr);
  return arr;
}

DirectedConnection** Context::newDirectedConnectionPtrArray(int size) {
    DirectedConnection** arr = (DirectedConnection**) malloc(sizeof(DirectedConnection*) * size);
    directedConnectionPtrArrays.push_back(arr);
    return arr;
}

DirectedInstance** Context::newDirectedInstancePtrArray(int size) {
    DirectedInstance** arr = (DirectedInstance**) malloc(sizeof(DirectedInstance*) * size);
    directedInstancePtrArrays.push_back(arr);
    return arr;
}

void* Context::saveArg(shared_ptr<Arg> arg) { 
  void* key = arg.get();
  argList[key] = arg;
  return key;
}

ArgPtr Context::getSavedArg(void* arg) {
  ASSERT(argList.count(arg),"Missing Arg!");
  return argList[arg];
}

Context* newContext() {
  Context* m = new Context();
  return m;
}

void deleteContext(Context* m) { 
  delete m;
}


} //CoreIR namespace
