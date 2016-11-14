#ifndef MAGMAIR_CPP_
#define MAGMAIR_CPP_

#include "enums.hpp"
#include "magmair.hpp"
#include <cassert>
#include <vector>

using namespace std;

// Should this be stored in the Module itself?

string WireBundleEnum2Str(WireBundleEnum wb) {
  switch(wb) {
    case IFACE: return "Interface";
    case INST: return "Instance";
    case SEL: return "Select";
    case IDX: return "Index";
  }
  assert(false);
}
Module::Module(string name, Type* type) : Circuit(false,name,type) {
  interface = new Interface(this,type->flip());
  cache = new WireBundleCache();
}

Module::~Module() {
  //Delete interface, instances, cache
  delete interface;
  instances.clear();
  delete cache;
}
WireBundleCache* Module::getCache() { return cache;}

void Primitive::print(void) {
  cout << "Primitive: " << name << "\n";
  cout << "  Type: " << type->_string() << "\n\n";
}

void Module::print(void) {
  cout << "Module: " << name << "\n";
  cout << "  Type: " << type->_string() << "\n";
  cout << "  Instances:\n";
  vector<Instance*>::iterator it1;
  for (it1=instances.begin(); it1!=instances.end(); ++it1) {
    cout << "    " << (*it1)->_string() << " : " << (*it1)->getCircuitType()->getName() << "\n";
  }
  cout << "  Connections:\n";
  vector<Connection>::iterator it2;
  for (it2=connections.begin(); it2!=connections.end(); ++it2) {
    cout << "    " << it2->first->_string() << " <=> " << it2->second->_string() << "\n" ;
  }
  cout << "\n";
}

Instance* Module::newInstance(string name,Circuit* circuitType) {
  Instance* inst = new Instance(this,circuitType->getType(),name,circuitType);
  instances.push_back(inst);
  return inst;
}
Interface* Module::getInterface(void) {
  return interface;
}
void Module::newConnect(WireBundle* a, WireBundle* b) {
  Connection con = std::make_pair(a,b);
  connections.push_back(con);
}

void WireBundle::addChild(WireBundle* wb) {
  children.push_back(wb);
}


//TODO Find a principled way to deal with select/index errors 
// Should I return a nullptr or create error message
Select* WireBundle::sel(string sel) {
  assert(type->isType(RECORD));
  Type* selType = ((RecordType*)type)->sel(sel);
  assert(selType);
  return container->getCache()->newSelect(container,selType,this,sel);
}

Index* WireBundle::idx(uint idx) {
  assert(type->isType(ARRAY));
  Type* idxType = ((ArrayType*)type)->idx();
  assert(idxType);
  return container->getCache()->newIndex(container,idxType,this,idx);
}
void WireBundle::setWired() {
  _wired = true;
  vector<WireBundle*>::iterator it;
  for (it=children.begin(); it!=children.end(); ++it) {
    (*it)->setWired();
  }
}

Select::Select(Module* container, Type* type, WireBundle* parent, string sel) : WireBundle(SEL,container,type), parent(parent), sel(sel) {
  //Add this to children of parent
  parent->addChild(this);
  
  //If Parent is wired, then this is wired.
  _wired = parent->isWired();
}

Index::Index(Module* container,Type* type, WireBundle* parent, uint idx) : WireBundle(IDX,container,type), parent(parent), idx(idx) {
  parent->addChild(this);

  _wired = parent->isWired();
}

WireBundleCache::~WireBundleCache() {
  map<SelectParamType,Select*>::iterator it1;
  for (it1=SelectCache.begin(); it1!=SelectCache.end(); ++it1) {
    delete it1->second;
  }
  
  map<IndexParamType,Index*>::iterator it2;
  for (it2=IndexCache.begin(); it2!=IndexCache.end(); ++it2) {
    delete it2->second;
  }

}
Select* WireBundleCache::newSelect(Module* container, Type* type, WireBundle* parent, string sel) {
  SelectParamType params = std::make_tuple(type,parent,sel);
  map<SelectParamType,Select*>::iterator it = SelectCache.find(params);
  if (it != SelectCache.end()) {
    return it->second;
  } else {
    Select* newSelect = new Select(container,type,parent,sel);
    SelectCache.emplace(params,newSelect);
    return newSelect;
  }
}

Index* WireBundleCache::newIndex(Module* container, Type* type, WireBundle* parent, uint idx) {
  IndexParamType params = std::make_tuple(type,parent,idx);
  map<IndexParamType,Index*>::iterator it = IndexCache.find(params);
  if (it != IndexCache.end()) {
    return it->second;
  } else {
    Index* newIndex = new Index(container,type,parent,idx);
    IndexCache.emplace(params,newIndex);
    return newIndex;
  }
}

string WireBundle::_string() {
  return WireBundleEnum2Str(bundleType);
}
string Interface::_string() {
  return container->getName();
}
string Instance::_string() {
  return name;
}

string Select::_string() {
  return parent->_string() + "." + sel;
}
string Index::_string() {
  return parent->_string() + "[" + to_string(idx) + "]";
}


void Connect(WireBundle* a, WireBundle* b) {
  //Make sure you are connecting within the same container
  if (a->getContainer()!=b->getContainer()) {
    cout << "ERROR: Connections can only occur within the same module\n";
    cout << "  Module of " <<a->_string() << ": " << a->getContainer()->getName() << "\n";
    cout << "  Module of " <<b->_string() << ": " << b->getContainer()->getName() << "\n";  exit(0);
  }
  Module* container = a->getContainer();
  Type* aType = a->getType();
  Type* bType = b->getType();
  //Make sure the flip of the types match
  if(a->getType() != b->getType()->flip()) {
    cout << "ERROR: Cannot connect these two types\n";
    cout << "  " << a->_string() << ": " << a->getType()->_string() << "\n";
    cout << "  " << b->_string() << ": " << b->getType()->_string() << "\n";
    exit(0);
  }
  
  //Make sure 'a' is not already wired (if has inputs)
  if (aType->hasInput() && a->isWired()) {
    cout << "ERROR: " << a->_string() << " has inputs and is already connected!\n";
    exit(0);
  }
  //Make sure 'b' is not already wired (if has inputs)
  if (bType->hasInput() && b->isWired()) {
    cout << "ERROR: " << b->_string() << " has inputs and is already connected!\n";
    exit(0);
  }
  //Make sure 'a' does not have children alreay wired (that are inputs)
  if (a->hasChildrenWired()) {
    cout << "ERROR: " << a->_string() << "has children(inputs) already connected!\n";
    exit(0);
  }
  if (b->hasChildrenWired()) {
    cout << "ERROR: " << b->_string() << "has children(inputs) already connected!\n";
    exit(0);
  }

  //Update 'a' and 'b' (and children)
  a->setWired();
  b->setWired();
  
  //Update parents if we are wiring inputs
  if (aType->hasInput()) {
    a->setChildrenWired(); //TODO rethink these confusing names
  }
  if (bType->hasInput()) {
    b->setChildrenWired();
  }

  container->newConnect(a,b);
}

Type* getType(Circuit* c) {
  return c->getType();
}

#endif //MAGMAIR_CPP_
