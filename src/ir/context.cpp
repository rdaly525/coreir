#include "coreir/ir/context.h"
#include "coreir/ir/typecache.h"
#include "coreir/ir/valuecache.h"
#include "coreir/ir/passmanager.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/dynamic_bit_vector.h"
#include "coreir/ir/error.h"
#include "coreir/ir/passes.h"
#include "coreir/ir/valuetype.h"
#include "coreir/ir/value.h"
#include "coreir/ir/types.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/module.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/common.h"
#include "coreir/ir/coreirlib.h"

using namespace std;

namespace CoreIR {
//TODO sketchy
#include "headers/core.hpp"
#include "headers/corebit.hpp"
#include "headers/memories.hpp"
#include "headers/mantle.hpp"


Context::Context() : maxErrors(8) {
  libmanager = new CoreIRLibrary(this);
  global = newNamespace("global");
  Namespace* pt = newNamespace("_");
  //This defines a passthrough module. It is basically a nop that just passes the signal through
  
  typecache = new TypeCache(this);
  valuecache = new ValueCache(this);
  //Automatically load coreir //defined in coreirprims.h
  CoreIRLoadHeader_core(this);
  CoreIRLoadHeader_corebit(this);
  CoreIRLoadHeader_memory(this);
  CoreIRLoadHeader_mantle(this);
  
  pm = new PassManager(this);
  Params passthroughParams({
    {"type",CoreIRType::make(this)},
  });
  TypeGen* passthroughTG = pt->newTypeGen(
    "passthrough",
    passthroughParams,
    [](Context* c, Values args) {
      Type* t = args.at("type")->get<Type*>();
      return c->Record({
        {"in",t->getFlipped()},
        {"out",t}
      });
    }
  );
  pt->newGeneratorDecl("passthrough",passthroughTG,passthroughParams);


}

// Order of this matters
Context::~Context() {
  delete pm;
  for (auto it : recordParamsList) delete it;
  for (auto it : paramsList) delete it;
  for (auto it : connectionPtrArrays) free(it);
  for (auto it : connectionArrays) free(it);
  for (auto it : wireableArrays) free(it);
  for (auto it : constStringArrays) free(it);
  for (auto it : stringArrays) free(it);
  for (auto it : stringBuffers) free(it);
  for (auto it : directedConnectionPtrArrays) free(it);
  for (auto it : directedInstancePtrArrays) free(it);
  for (auto it : valuePtrArrays) free(it);
  for (auto it : valueTypePtrArrays) free(it);

  delete typecache;
  for (auto it : namespaces) delete it.second;
  delete valuecache;
  delete libmanager;
}

std::map<std::string,Namespace*> Context::getNamespaces() {
  std::map<std::string,Namespace*> tmp;
  for (auto ns : namespaces) {
    if (ns.first!="_") tmp.emplace(ns);
  }
  return tmp;
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
  assert(0);
}


Namespace* Context::newNamespace(string name) { 
  checkStringSyntax(name);
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

GlobalValue* Context::getGlobalValue(std::string ref) {
  vector<string> refsplit = splitRef(ref);
  ASSERT(hasNamespace(refsplit[0]),"Missing namespace: " + refsplit[0]);
  Namespace* ns = getNamespace(refsplit[0]);
  if (ns->hasGenerator(refsplit[1])) return ns->getGenerator(refsplit[1]);
  if (ns->hasModule(refsplit[1])) return ns->getModule(refsplit[1]);
  ASSERT(0,"MISSING " + ref);
  return nullptr;
}
bool Context::hasGenerator(std::string ref) {
  vector<string> refsplit = splitRef(ref);
  if (!hasNamespace(refsplit[0])) return false;
  Namespace* ns = getNamespace(refsplit[0]);
  return ns->hasGenerator(refsplit[1]);
}
bool Context::hasModule(std::string ref) {
  vector<string> refsplit = splitRef(ref);
  if (!hasNamespace(refsplit[0])) return false;
  Namespace* ns = getNamespace(refsplit[0]);
  return ns->hasModule(refsplit[1]);
}
bool Context::hasGlobalValue(std::string ref) {
  vector<string> refsplit = splitRef(ref);
  if (!hasNamespace(refsplit[0])) return false;
  Namespace* ns = getNamespace(refsplit[0]);
  return ns->hasGlobalValue(refsplit[1]);
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

bool Context::runPassesOnAll(std::vector<std::string> order) {
  assert(pm);
  vector<string> namespaces;
  for (auto npair : this->getNamespaces()) {
    namespaces.push_back(npair.first);
  }
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

BitType* Context::Bit() { return typecache->getBit(); }
BitInType* Context::BitIn() { return typecache->getBitIn(); }
BitInOutType* Context::BitInOut() { return typecache->getBitInOut(); }  
ArrayType* Context::Array(uint n, Type* t) { return typecache->getArray(n,t);}
RecordType* Context::Record(RecordParams rp) { return typecache->getRecord(rp); }
NamedType* Context::Named(string nameref) {
  vector<string> split = splitRef(nameref);
  ASSERT(this->hasNamespace(split[0]),"Missing Namespace + " + split[0]);
  ASSERT(this->getNamespace(split[0])->hasNamedType(split[1]),"Missing Named type + " + nameref);
  return this->getNamespace(split[0])->getNamedType(split[1]);
}

Type* Context::Flip(Type* t) { return t->getFlipped();}

Type* Context::In(Type* t) {
    assert(!t->isMixed() && "can't make all input if part are in and part are out");
    if (t->isInput()) {
        return t;
    }
    else {
        return t->getFlipped();
    }
}

Type* Context::Out(Type* t) {
    assert(!t->isMixed() && "can't make all output if part are in and part are out");
    if (t->isInput()) {
        return t->getFlipped();
    }
    else {
        return t;
    }
}

AnyType* Context::Any() { return AnyType::make(this);}
BoolType* Context::Bool() { return BoolType::make(this);}
IntType* Context::Int(){ return IntType::make(this);}
BitVectorType* Context::BitVector(int width) { return BitVectorType::make(this,width);}
StringType* Context::String() { return StringType::make(this);}
//CoreIRType* Context::CoreIRType() { return CoreIRType::make(this);}

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

void Context::removeTop() {
  this->top = nullptr;
}


bool Context::hasTypeGen(string nameref) {
  vector<string> split = splitRef(nameref);
  if (!this->hasNamespace(split[0])) {
    return false;
  }
  if(!this->getNamespace(split[0])->hasTypeGen(split[1])) {
    return false;
  }
  return true;
  
}

TypeGen* Context::getTypeGen(string nameref) {
  ASSERT(this->hasTypeGen(nameref),"Missing Typegen: " + nameref);
  vector<string> split = splitRef(nameref);
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

Values* Context::newValues() {
  Values* vals = new Values();
  valuesList.push_back(vals);
  return vals;
}

Value** Context::newValueArray(int size) {
    Value** arr = (Value**) malloc(sizeof(Value*) * size);
    valuePtrArrays.push_back(arr);
    return arr;
}

ValueType** Context::newValueTypeArray(int size) {
    ValueType** arr = (ValueType**) malloc(sizeof(ValueType*) * size);
    valueTypePtrArrays.push_back(arr);
    return arr;
}

Type** Context::newTypeArray(int size) {
    Type** arr = (Type**) malloc(sizeof(Type*) * size);
    typePtrArrays.push_back(arr);
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


Context* newContext() {
  Context* m = new Context();
  return m;
}

void deleteContext(Context* m) { 
  delete m;
}


} //CoreIR namespace
