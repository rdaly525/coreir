#include "coreir/ir/wireable.h"
#include "coreir/ir/common.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/context.h"
#include "coreir/ir/instantiable.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/error.h"
#include "coreir/ir/types.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/value.h"


using namespace std;

///////////////////////////////////////////////////////////
//----------------------- Wireables ----------------------//
///////////////////////////////////////////////////////////

namespace CoreIR {

const string Interface::instname = "self";

Wireable::~Wireable() {
  for (auto selmap : selects) {
    delete selmap.second;
  }
}

Select* Wireable::sel(string selStr) {
  if (selects.count(selStr)) {
    return selects[selStr];
  }
  ASSERT(type->canSel(selStr),"Cannot select " + selStr + " From " + this->toString() + "\n  Type: " + type->toString());

  Select* select = new Select(this->getContainer(),this,selStr, type->sel(selStr));
  selects[selStr] = select;
  return select;
}

Select* Wireable::sel(uint selStr) { return sel(to_string(selStr)); }

Select* Wireable::sel(SelectPath path) {
  Wireable* ret = this;
  for (auto selstr : path) ret = ret->sel(selstr);
  return cast<Select>(ret);
}

Select* Wireable::sel(std::initializer_list<const char*> path) {
  return sel(SelectPath(path.begin(),path.end()));
}
Select* Wireable::sel(std::initializer_list<std::string> path) {
  return sel(SelectPath(path.begin(),path.end()));
}



bool Wireable::canSel(string selstr) {
  return type->canSel(selstr);
}

ConstSelectPath Wireable::getConstSelectPath() {
  Wireable* top = this;
  ConstSelectPath path;
  while(auto s = dyn_cast<Select>(top)) {
    path.insert(path.begin(), s->getSelStr());
    top = s->getParent();
  }
  if (auto iface = dyn_cast<Interface>(top)) {
    const string& instname = iface->getInstname();
    path.insert(path.begin(), instname);
  }
  else if (auto inst = dyn_cast<Instance>(top)) {
    const string& instname = inst->getInstname();
    path.insert(path.begin(), instname);
  }
  else {
    ASSERT(0,"Cannot be here")
  }
  return path;
}

void Wireable::connect(Wireable* w) {
  this->getContainer()->connect(this,w);
}

void Wireable::disconnect() {
  this->getContainer()->disconnect(this);
}

void Wireable::disconnectAll() {
  for (auto sels : this->getSelects()) {
    sels.second->disconnectAll();
  }
  this->disconnect();
}

void Wireable::removeSel(string selStr) {
  ASSERT(selects.count(selStr),"Cannot remove " + selStr + "Because it does not exist!");
  Select* s = selects[selStr];
  selects.erase(selStr);
  delete s;
}


SelectPath Wireable::getSelectPath() {
  Wireable* top = this;
  SelectPath path;
  while(auto s = dyn_cast<Select>(top)) {
    path.push_front(s->getSelStr());
    top = s->getParent();
  }
  if (isa<Interface>(top))
    path.push_front("self");
  else { //This should be an instance
    string instname = cast<Instance>(top)->getInstname();
    path.push_front(instname);
  }
  return path;
}

Context* Wireable::getContext() { return container->getContext();}
string Wireable::wireableKind2Str(WireableKind wb) {
  switch(wb) {
    case WK_Interface: return "Interface";
    case WK_Instance: return "Instance";
    case WK_Select: return "Select";
  }
  ASSERT(false,"Unknown WireableKind: " + to_string(wb));
}

LocalConnections Wireable::getLocalConnections() {
  //For the annoying case where connections connect bact to self
  Connections uniqueCons;
  LocalConnections cons;
  std::function<void(Wireable*)> traverse;
  traverse = [&cons,&traverse,&uniqueCons](Wireable* curw) ->void {
    for (auto other : curw->getConnectedWireables()) {
      auto check = connectionCtor(curw,other);
      if (uniqueCons.count(check)==0) {
        cons.push_back({curw,other});
        uniqueCons.insert(check);
      }
    }
    for (auto sels : curw->getSelects()) {
      traverse(sels.second);
    }
  };

  traverse(this);
  return cons;
}

Wireable* Wireable::getTopParent() {
  Wireable* top = this;
  while (auto wsel = dyn_cast<Select>(top)) {
    top = wsel->getParent();
  }
  return top;
}


Instance::Instance(ModuleDef* container, string instname, Module* moduleRef, Values modargs) : Wireable(WK_Instance,container,nullptr), instname(instname), moduleRef(moduleRef), isgen(false) {
  ASSERT(moduleRef,"Module is null, in inst: " + this->getInstname());
  //First merge default args
  mergeValues(modargs,moduleRef->getDefaultModArgs());
  //Check if modargs is the same as expected by ModuleRef
  checkValuesAreParams(modargs,moduleRef->getModParams());
  this->modargs = modargs;

  //TODO checkif instname is unique
  this->type = moduleRef->getType();
}

Instance::Instance(ModuleDef* container, string instname, Generator* generatorRef, Values genargs, Values modargs) : Wireable(WK_Instance,container,nullptr), instname(instname), isgen(true), generatorRef(generatorRef) {
  ASSERT(generatorRef,"Generator is null, in inst: " + this->getInstname());
  mergeValues(genargs,generatorRef->getDefaultGenArgs());
  checkValuesAreParams(genargs,generatorRef->getGenParams());
  this->genargs = genargs;
  this->type = generatorRef->getTypeGen()->getType(genargs);
  ASSERT(isa<RecordType>(this->type),"Generated type needs to be a record but is: " + this->type->toString());
  auto mpair = generatorRef->getModParams(genargs);
  mergeValues(modargs,mpair.second);
  checkValuesAreParams(modargs,mpair.first);
  this->modargs = modargs;
}

string Interface::toString() const{
  return "self";
}

string Instance::toString() const {
  return instname;
}

Instantiable* Instance::getInstantiableRef() {
  if (isgen) return generatorRef;
  else return moduleRef;
}

bool Instance::runGenerator() {
  ASSERT(generatorRef,"Not a Generator Instanc! in " + this->getInstname());
  //If we have already run the generator, do not run again
  if (moduleRef) return false;

  //TODO should this be the default behavior?
  //If there is no generatorDef, then just do nothing
  if (!generatorRef->hasDef()) return false;

  //Actually run the generator
  this->moduleRef = generatorRef->getModule(genargs);
  assert(moduleRef->hasDef());

  //Change this instance to a Module
  isgen = false;
  wasgen = true;
  return true;
}

void Instance::replace(Module* moduleRef, Values modargs) {
  ASSERT(!this->isGen(),"NYI, Cannot replace a generator instance with a module isntance")
  ASSERT(this->getType()==moduleRef->getType(),"NYI, Cannot replace with a different type")
  ASSERT(moduleRef,"ModuleRef is null in inst: " + this->getInstname());
  this->moduleRef = moduleRef;
  this->modargs = modargs;
  checkValuesAreParams(modargs,moduleRef->getModParams());
}

//TODO this is probably super unsafe and will leak memory
//TODO I do not think this deals with default args
void Instance::replace(Generator* generatorRef, Values genargs, Values modargs) {
  ASSERT(generatorRef,"Generator is null! in inst: " + this->getInstname());
  ASSERT(this->isGen(),"NYI, Cannot replace a generator instance with a module isntance");

  this->generatorRef = generatorRef;
  checkValuesAreParams(genargs,generatorRef->getGenParams());
  this->genargs = genargs;
  Type* newType = generatorRef->getTypeGen()->getType(genargs);
  ASSERT(this->getType() == newType,"NYI, Cannot replace with a different type");
  
  auto mpair = generatorRef->getModParams(genargs);
  mergeValues(modargs,mpair.second);
  checkValuesAreParams(modargs,mpair.first);
  this->modargs = modargs;
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

} //CoreIR namesapce
