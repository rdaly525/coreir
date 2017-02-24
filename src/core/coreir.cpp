#ifndef COREIR_CPP_
#define COREIR_CPP_

#include "enums.hpp"
#include "coreir.hpp"
#include "typedcoreir.hpp"
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

ModuleDef::ModuleDef(string name, Type* type,InstantiableKind e) : Instantiable(e,"",name), type(type), verilog("") {
  interface = new Interface(this);
  cache = new SelCache();
}

ModuleDef::~ModuleDef() {
  //Delete interface, instances, cache
  delete interface;
  for(auto inst : instances) delete inst;
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

Instance* ModuleDef::addInstance(string instname, Instantiable* m,GenArgs* genargs) {
  Instance* inst = new Instance(this,instname,m,genargs);
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
  
  //Update 'a' and 'b'
  a->wire->addWiring(b->wire);
  b->wire->addWiring(a->wire);
 
  wirings.push_back({a,b});
}

///////////////////////////////////////////////////////
//----------------------- Wire ----------------------//
///////////////////////////////////////////////////////

void Wire::addChild(string selStr, Wire* w) {
  children.emplace(selStr,w);
}

void Wire::addWiring(Wire* w) {
  wirings.push_back(w);
}


string Wire::toString() const {
  return "NYI: Wire string";
}
///////////////////////////////////////////////////////////
//----------------------- Wireables ----------------------//
///////////////////////////////////////////////////////////

Select* Wireable::sel(string selStr) {
  return container->getCache()->newSelect(container,this,selStr);
}

Select* Wireable::sel(uint selStr) { return sel(to_string(selStr)); }

string Interface::toString() const{
  return container->getName();
}

string Instance::toString() const {
  return instname;
}

string Select::toString() const {
  string ret = parent->toString(); 
  if (isNumber(selStr)) return ret + "[" + selStr + "]";
  return ret + "." + selStr;
}

std::ostream& operator<<(ostream& os, const Wireable& i) {
  os << i.toString();
  return os;
}

///////////////////////////////////////////////////////////
//-------------------- SelCache --------------------//
///////////////////////////////////////////////////////////

SelCache::~SelCache() {
  for (auto sel : cache) delete sel.second;
  for (auto tsel : typedcache) delete tsel.second;
}

Select* SelCache::newSelect(ModuleDef* container, Wireable* parent, string selStr) {
  SelectParamType params = {parent,selStr};
  auto it = cache.find(params);
  if (it != cache.end()) {
    return it->second;
  } 
  else {
    Select* s = new Select(container,parent,selStr);
    cache.emplace(params,s);
    return s;
  }
}

TypedSelect* SelCache::newTypedSelect(ModuleDef* container, Wireable* parent, Type* type, string selStr) {
  assert(parent->isTyped());
  SelectParamType params = {parent,selStr};
  auto it = typedcache.find(params);
  if (it != typedcache.end()) {
    return it->second;
  } 
  else {
    //TypedWire* twire = castTypedWire(parent->wire);
    assert(castTypedWire(parent->wire));
    TypedModuleDef* tcontainer = safecast<TypedModuleDef*>(container);
    TypedSelect* ts = new TypedSelect(tcontainer,type,parent,selStr);
    cache.emplace(params,ts);
    return ts;
  }
}



#endif //COREIR_CPP_
