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


ModuleDef::ModuleDef(string name, string nameSpace, Type* type) : Instantiable(MDEF,name,nameSpace), type(type) {
  interface = new Interface(this);
  cache = new WireableCache();
}

ModuleDef::~ModuleDef() {
  //Delete interface, instances, cache
  delete interface;
  for(vector<Instance*>::iterator it=instances.begin(); it!=instances.end(); ++it) delete (*it);
  delete cache;
}


void ModuleDef::print(void) {
  cout << "ModuleDef: " << name << "\n";
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
WireableCache* ModuleDef::getCache() { return cache;}

Instance* ModuleDef::addInstance(string name, ModuleDef* m) {
  Instance* inst = new Instance(this,name,m);
  instances.push_back(inst);
  return inst;
}
Instance* ModuleDef::addInstance(string name, ModuleDecl* m) {
  Instance* inst = new Instance(this,name,m);
  instances.push_back(inst);
  return inst;
}
Instance* ModuleDef::addInstance(string name, GeneratorDecl* m, Type* genParamsType, void* genParams) {
  GenInstance* inst = new GenInstance(this,name,m,genParamsType,genParams);
  instances.push_back(inst);
  return inst;
}

void ModuleDef::Connect(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same container
  if (a->getContainer()!=this || b->getContainer() != this) {
    cout << "ERROR: Connections can only occur within the same module\n";
    cout << "  This ModuleDef: "  << this->getName() << endl;
    cout << "  ModuleDef of " <<a->toString() << ": " << a->getContainer()->getName() << endl;
    cout << "  ModuleDef of " <<b->toString() << ": " << b->getContainer()->getName() << endl;
    exit(0);
  }
  
  //Update 'a' and 'b' (and children)
  a->addConnection(b);
  b->addConnection(a);
 
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
Select* WireableCache::newSelect(ModuleDef* container, Wireable* parent, string selStr) {
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


///////////////////////////////////////////////////////////
//----------------------- NameSpace ---------------------//
///////////////////////////////////////////////////////////

NameSpace::~NameSpace() {
  for(map<string,ModuleDef*>::iterator it=modList.begin(); it!=modList.end(); ++it)
    delete it->second;
}

//TODO add the verilog and sim stuff
ModuleDef* NameSpace::defineModuleDef(string name,Type* type) {
  ModuleDef* m = new ModuleDef(name,this->name, type);
  modList.emplace(name,m);
  return m;
}

void NameSpace::defineGenerator(string name,genfun_t gen) {
  genList.emplace(name,gen);
}

void NameSpace::addDefinedModuleDef(string name, ModuleDef* m) {
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

CoreIRContext* newContext() {
  CoreIRContext* m = new CoreIRContext();
  return m;
}

void deleteContext(CoreIRContext* m) { delete m;}

GeneratorDecl* CoreIRContext::declareGen(string nameSpace,string name) { 
  GeneratorDecl* og = new GeneratorDecl(nameSpace,name);
  opaques.push_back(og);
  return og;
}

ModuleDecl* CoreIRContext::declareMod(string nameSpace, string name) {
  ModuleDecl* m = new ModuleDecl(nameSpace,name);
  opaques.push_back(m);
  return m;
}

void compile2Verilog(ModuleDef* m) {
  cout << "PRINTING VERILOG\n";
}

uint8_t isDirty(dirty_t* d) {
  return d->dirty;
}
void setDirty(dirty_t* d) {
  d->dirty = 1;
}


#endif //COREIR_CPP_
