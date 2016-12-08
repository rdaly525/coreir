#ifndef COREIR_CPP_
#define COREIR_CPP_

#include "enums.hpp"
#include "coreir.hpp"
#include <cassert>
#include <vector>
#include <set>

using namespace std;

///////////////////////////////////////////////////////////
//-------------------- Instantiable ---------------------//
///////////////////////////////////////////////////////////

ostream& operator<<(ostream& os, const Instantiable& i) {
  os << i.toString();
  return os;
}


ModuleDef::ModuleDef(string name, Type* type) : Instantiable(MDEF,"",name), type(type) {
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
  for (auto inst : instances) {
    cout << "    " << (*inst) << endl;
  }
  cout << "  Wirings:\n";
  for (auto wiring : wirings) {
    cout << "    " << *(wiring.first) << " <=> " << *(wiring.second) << "\n" ;
  }
  cout << endl;
}

Instance* ModuleDef::addInstance(string name, Instantiable* m,Genargs* genargs) {
  Instance* inst = new Instance(this,name,m,genargs);
  instances.push_back(inst);
  return inst;
}

void ModuleDef::wire(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same container
  if (a->getContainer()!=this || b->getContainer() != this) {
    cout << "ERROR: Wirings can only occur within the same module\n";
    cout << "  This ModuleDef: "  << this->getName() << endl;
    cout << "  ModuleDef of " <<a->toString() << ": " << a->getContainer()->getName() << endl;
    cout << "  ModuleDef of " <<b->toString() << ": " << b->getContainer()->getName() << endl;
    exit(0);
  }
  
  //Update 'a' and 'b' (and children)
  a->addWiring(b);
  b->addWiring(a);
 
  wirings.push_back({a,b});
}
// TODO THis shit is fucked.
//void ModuleDef::setNameSpace(NameSpace* _ns) {
//  //ns->removeModDef(this);
//  ns = _ns;
//}
Genargs::Genargs(Type* type) : type(type) {
  data = allocateFromType(type);
}

Genargs::~Genargs() {
  deallocateFromType(type,data);
}

///////////////////////////////////////////////////////////
//----------------------- Wireable ----------------------//
///////////////////////////////////////////////////////////

void Wireable::addChild(string selStr, Wireable* wb) {
  children.emplace(selStr,wb);
}

void Wireable::addWiring(Wireable* w) {
  wirings.push_back(w);
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
  for(auto modhash : modList) delete modhash.second;
  for(auto genhash : genList) delete genhash.second;
}

ModuleDef* NameSpace::moduleDefLookup(string name) {
  auto it = modList.find(name);
  if (it != modList.end()) return it->second;
  throw "Could not find module " + name + " in namespace " + nameSpace;
}

GeneratorDef* NameSpace::generatorDefLookup(string name) {
  auto it = genList.find(name);
  if (it != genList.end()) return it->second;
  throw "Could not find gen " + name + " in namespace " + nameSpace;
}


void NameSpace::addGeneratorDef(GeneratorDef* g) {
  genList.emplace(g->getName(),g);
}

void NameSpace::addModuleDef(ModuleDef* m) {
  modList.emplace(m->getName(),m);
}

CoreIRContext::CoreIRContext() {
  global = new NameSpace("global");
}

CoreIRContext::~CoreIRContext() {
  delete global;
  for (auto it : libs) delete it.second;
  for (auto it : opaques) delete it;
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
NameSpace* CoreIRContext::nameSpaceLookup(string nameSpace) {
  auto it = libs.find(nameSpace);
  if (it!=libs.end()) return it->second;
  throw "Cannot find namespace: " + nameSpace;
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


void compile(CoreIRContext* c, ModuleDef* m) {
  cout << "COMPILING!!\n";
  set<ModuleDef*>* resolvedMods = new set<ModuleDef*>;
  try {
    resolve(c,m,resolvedMods);
  } 
  catch(string e) {
    cout << "ERROR: " << e << endl;
    delete resolvedMods;
    exit(0);
  }
  delete resolvedMods;
  cout << "DONE COMPILING!!\n";
   // ModuleDef* typed = typecheck(m);
}

//This function mutates the current moduleDef recursively to
//  replace all ModuleDecl with ModuleDef
//  replace all GeneratorDecl with ModuleDef
//resolvedMods keeps getting added to
void resolve(CoreIRContext* c, ModuleDef* m, set<ModuleDef*>* resolvedMods) {
  
  //Do not do any recompute if module already resolved
  if (resolvedMods->find(m) != resolvedMods->end()) return;
  cout << "Started Resolving: " << m->toString() << endl;

  //For each instance compute if necessary and then resolve recursively
  for (auto inst : m->getInstances()) {
    Instantiable* instRef = inst->getInstRef();
    ModuleDef* modDef;
    string nameSpace = instRef->getNameSpaceStr();
    if (instRef->isType(MDEF) ) {
      modDef = (ModuleDef*) instRef;
    }
    else if (instRef->isType(MDEC) ) {
      NameSpace* n = c->nameSpaceLookup(nameSpace);
      modDef = n->moduleDefLookup(instRef->getName());
      inst->replace(modDef);
    }
    else if (instRef->isType(GDEC) ) {
      NameSpace* n = c->nameSpaceLookup(nameSpace);
      GeneratorDef* genDef = n->generatorDefLookup(instRef->getName());
      //Generate the module in the global namespace
      modDef = genDef->getGenfun()(c->getGlobal(),inst->getGenargs());
      inst->replace(modDef);
    } else {
      throw "FUCK";
    }
    resolve(c,modDef,resolvedMods);
  }
  cout << "Finished Resolving: " << m->toString() << endl;
  resolvedMods->insert(m);
}


#endif //COREIR_CPP_
