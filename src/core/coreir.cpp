#ifndef COREIR_CPP_
#define COREIR_CPP_

#include "enums.hpp"
#include "coreir.hpp"
#include <cassert>
#include <vector>

using namespace std;

///////////////////////////////////////////////////////////
//-------------------- Instantiable ---------------------//
///////////////////////////////////////////////////////////

ostream& operator<<(ostream& os, const Instantiable& i) {
  os << i.toString();
  return os;
}


Module::Module(string name, string nameSpace, Type* type) : Instantiable(MOD,name,nameSpace), type(type) {
  interface = new Interface(this);
  cache = new WireableCache();
}

Module::~Module() {
  //Delete interface, instances, cache
  delete interface;
  for(vector<Instance*>::iterator it=instances.begin(); it!=instances.end(); ++it) delete (*it);
  delete cache;
}


void Module::print(void) {
  cout << "Module: " << name << "\n";
  cout << "  Type: " << (*type) << "\n";
  cout << "  Instances:\n";
  vector<Instance*>::iterator it1;
  for (it1=instances.begin(); it1!=instances.end(); ++it1) {
    cout << "    " << (**it1) << endl;
  }
  cout << "  Connections:\n";
  vector<Connection>::iterator it2;
  for (it2=connections.begin(); it2!=connections.end(); ++it2) {
    cout << "    " << *(it2->first) << " <=> " << *(it2->second) << "\n" ;
  }
  cout << "\n";
}
WireableCache* Module::getCache() { return cache;}

Instance* Module::addInstance(string name, Module* m) {
  Instance* inst = new Instance(this,name,m);
  instances.push_back(inst);
  return inst;
}
Instance* Module::addInstance(string name, OpaqueModule* m) {
  Instance* inst = new Instance(this,name,m);
  instances.push_back(inst);
  return inst;
}
Instance* Module::addInstance(string name, OpaqueGenerator* m, Type* genParamsType, void* genParams) {
  GenInstance* inst = new GenInstance(this,name,m,genParamsType,genParams);
  instances.push_back(inst);
  return inst;
}


void Module::newConnect(Wireable* a, Wireable* b) {
  connections.push_back({a,b});
}

///////////////////////////////////////////////////////////
//----------------------- Wireable ----------------------//
///////////////////////////////////////////////////////////

void Wireable::addChild(string selStr, Wireable* wb) {
  children.emplace(selStr,wb);
}

void Wireable::addConnection(Wireable* w) {
  connections.push_back(w);
}

Select* Wireable::sel(string selStr) {
  return container->getCache()->newSelect(container,this,selStr);
}

Select* Wireable::sel(uint idx) {
  return container->getCache()->newSelect(container,this,to_string(idx));
}

string Interface::toString() const{
  return container->getName();
}

string Instance::toString() const {
  return name;
}

string Select::toString() const {
  string ret = parent->toString(); 
  bool isIdx = (selStr.find_first_not_of("0123456789")==string::npos);
  if (isIdx) return ret + "[" + selStr + "]";
  return ret + "." + selStr;
}

std::ostream& operator<<(ostream& os, const Wireable& i) {
  os << i.toString();
  return os;
}

///////////////////////////////////////////////////////////
//-------------------- WireableCache --------------------//
///////////////////////////////////////////////////////////

WireableCache::~WireableCache() {
  map<SelectParamType,Select*>::iterator it1;
  for (it1=SelectCache.begin(); it1!=SelectCache.end(); ++it1) {
    delete it1->second;
  }
}
Select* WireableCache::newSelect(Module* container, Wireable* parent, string selStr) {
  SelectParamType params = {parent,selStr};
  map<SelectParamType,Select*>::iterator it = SelectCache.find(params);
  if (it != SelectCache.end()) {
    return it->second;
  } else {
    Select* newSelect = new Select(container,parent,selStr);
    SelectCache.emplace(params,newSelect);
    return newSelect;
  }
}

void Connect(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same container
  if (a->getContainer()!=b->getContainer()) {
    cout << "ERROR: Connections can only occur within the same module\n";
    cout << "  Module of " <<a->toString() << ": " << a->getContainer()->getName() << "\n";
    cout << "  Module of " <<b->toString() << ": " << b->getContainer()->getName() << "\n";  exit(0);
  }
  Module* container = a->getContainer();
  
  //Update 'a' and 'b' (and children)
  a->addConnection(b);
  b->addConnection(a);
 
  container->newConnect(a,b);
}

///////////////////////////////////////////////////////////
//----------------------- NameSpace ---------------------//
///////////////////////////////////////////////////////////

NameSpace::~NameSpace() {
  for(map<string,Module*>::iterator it=modList.begin(); it!=modList.end(); ++it)
    delete it->second;
}

//TODO add the verilog and sim stuff
Module* NameSpace::defineModule(string name,Type* type) {
  Module* m = new Module(name,this->name, type);
  modList.emplace(name,m);
  return m;
}

void NameSpace::defineGenerator(string name,genfun_t gen) {
  genList.emplace(name,gen);
}

void NameSpace::addDefinedModule(string name, Module* m) {
  modList.emplace(name,m);
}
CoreIRContext::CoreIRContext() {
  global = new NameSpace("global");
}
CoreIRContext::~CoreIRContext() {
  delete global;
  for(map<string,NameSpace*>::iterator it=libs.begin(); it!=libs.end(); ++it)
    delete it->second;
  for(auto it=opaques.begin(); it!=opaques.end(); ++it) delete (*it);
}

NameSpace* CoreIRContext::registerLib(string name) {
  if (libs.find(name) != libs.end()) {
    cout << "ERROR: added lib twice: " << name << endl;
    exit(0);
  }
  NameSpace* lib = new NameSpace(name);
  libs.emplace(name,lib);
  return lib;
}

Module* CoreIRContext::defineModule(string name,Type* t) {
  return global->defineModule(name,t);
}

CoreIRContext* newContext() {
  CoreIRContext* m = new CoreIRContext();
  return m;
}

void deleteContext(CoreIRContext* m) { delete m;}

OpaqueGenerator* CoreIRContext::declareGen(string nameSpace,string name) { 
  OpaqueGenerator* og = new OpaqueGenerator(nameSpace,name);
  opaques.push_back(og);
  return og;
}

OpaqueModule* CoreIRContext::declareMod(string nameSpace, string name) {
  OpaqueModule* m = new OpaqueModule(nameSpace,name);
  opaques.push_back(m);
  return m;
}

void compile2Verilog(Module* m) {
  cout << "PRINTING VERILOG\n";
}

uint8_t isDirty(dirty_t* d) {
  return d->dirty;
}
void setDirty(dirty_t* d) {
  d->dirty = 1;
}


#endif //COREIR_CPP_
