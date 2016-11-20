#ifndef MAGMAIR_CPP_
#define MAGMAIR_CPP_

#include "enums.hpp"
#include "magmair.hpp"
#include <cassert>
#include <vector>

using namespace std;

// Should this be stored in the Module itself?

string WireableEnum2Str(WireableEnum wb) {
  switch(wb) {
    case IFACE: return "Interface";
    case INST: return "Instance";
    case SEL: return "Select";
  }
  assert(false);
}
Module::Module(string name, Type* type) : Circuit(false,name,type) {
  interface = new Interface(this,type->flip());
  cache = new WireableCache();
}

Module::~Module() {
  //Delete interface, instances, cache
  delete interface;
  instances.clear();
  delete cache;
}
WireableCache* Module::getCache() { return cache;}

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
void Module::newConnect(Wireable* a, Wireable* b) {
  Connection con = std::make_pair(a,b);
  connections.push_back(con);
}

void Wireable::addChild(string selStr, Wireable* wb) {
  children.emplace(selStr,wb);
}


//TODO Find a principled way to deal with select/index errors 
// Should I return a nullptr or create error message
Select* Wireable::sel(string selStr) {
  assert(type->isType(RECORD));
  Type* selType = ((RecordType*)type)->sel(selStr);
  assert(selType);
  return container->getCache()->newSelect(container,selType,this,selStr);
}

Select* Wireable::sel(uint idx) {
  assert(type->isType(ARRAY));
  Type* idxType = ((ArrayType*)type)->idx(idx);
  assert(idxType);
  return container->getCache()->newSelect(container,idxType,this,to_string(idx));
}

//Set _wired and all children's parentWired
void Wireable::addConnection(Wireable* w) {
  _wired = true;
  map<string,Wireable*>::iterator it;
  for (it=children.begin(); it!=children.end(); ++it) {
    it->second->setParentWired();
  }
  connections.push_back(w);
}

//Set _parentWired and all children's setParentWired
void Wireable::setParentWired() {
  _parentWired = true;
  map<string,Wireable*>::iterator it;
  for (it=children.begin(); it!=children.end(); ++it) {
    it->second->setParentWired();
  }
}

Select::Select(Module* container, Type* type, Wireable* parent, string selStr) : Wireable(SEL,container,type), parent(parent), selStr(selStr) {
  //Add this to children of parent
  parent->addChild(selStr,this);
  
  //If Parent is wired or parent has wired parents
  _parentWired = parent->isWired() || parent->isParentWired();
}

WireableCache::~WireableCache() {
  map<SelectParamType,Select*>::iterator it1;
  for (it1=SelectCache.begin(); it1!=SelectCache.end(); ++it1) {
    delete it1->second;
  }
}
Select* WireableCache::newSelect(Module* container, Type* type, Wireable* parent, string selStr) {
  SelectParamType params = std::make_tuple(type,parent,selStr);
  map<SelectParamType,Select*>::iterator it = SelectCache.find(params);
  if (it != SelectCache.end()) {
    return it->second;
  } else {
    Select* newSelect = new Select(container,type,parent,selStr);
    SelectCache.emplace(params,newSelect);
    return newSelect;
  }
}

string Wireable::_string() {
  return WireableEnum2Str(bundleType);
}
string Interface::_string() {
  return container->getName();
}
string Instance::_string() {
  return name;
}

string Select::_string() {
  string ret = parent->_string(); 
  bool isIdx = (selStr.find_first_not_of("0123456789")==string::npos);
  if (isIdx) return ret + "[" + selStr + "]";
  return ret + "." + selStr;
}

void Connect(Wireable* a, Wireable* b) {
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
  a->addConnection(b);
  b->addConnection(a);
  
  //Update parents if we are wiring inputs.
  //Confusing names. But this is setting the _childrenWired flag of the parents
  //  and NOT setting the _wired of the children lol
  if (aType->hasInput()) {
    a->setChildrenWired(); 
  }
  if (bType->hasInput()) {
    b->setChildrenWired();
  }

  container->newConnect(a,b);
}

//TODO make sure there exists at least 1 children given that _childrenWired is set
//TODO This definitely needs nice error messages
bool Wireable::checkWired() {
  if (_wired) return true;
  if (type->isBase()) return false;
  
  //Should have children...
  assert(type->isType(RECORD) || type->isType(ARRAY));
  
  //Check if all entries of map exist and are wired
  //Have to deal with Records and Arrays differently
  if(type->isType(RECORD)) {
    //iterate over type record keys
    map<string,Type*> record = ((RecordType*)type)->getRecord();
    map<string,Type*>::iterator tit;
    for (tit=record.begin(); tit!=record.end(); ++tit) {
      map<string,Wireable*>::iterator it = children.find(tit->first);
      if (it==children.end()) return false;
      if (!it->second->checkWired()) return false;
    }
  } else {
    // iterate over the array
    for (uint i=0; i<((ArrayType*)type)->getLen(); ++i) {
      map<string,Wireable*>::iterator it = children.find(to_string(i));
      if (it==children.end()) return false;
      if (!it->second->checkWired()) return false;
    }
  }
  return true;
  
}




Type* getType(Circuit* c) {
  return c->getType();
}

#endif //MAGMAIR_CPP_
