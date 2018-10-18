#include "coreir/ir/wireable.h"
#include "coreir/ir/common.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/context.h"
#include "coreir/ir/module.h"
#include "coreir/ir/generator.h"
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

Select* Wireable::sel(const std::string& selStr) {
  if (selects.count(selStr)) {
    return selects[selStr];
  }
  ASSERT(type->canSel(selStr),"Cannot select " + selStr + " From " + this->toString() + "\n  Type: " + type->toString());

  Select* select = new Select(this->getContainer(),this,selStr, type->sel(selStr));

  selects[selStr] = select;

  return select;
}

Select* Wireable::sel(uint selStr) { return sel(to_string(selStr)); }

Select* Wireable::sel(const SelectPath& path) {
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

bool Wireable::canSel(SelectPath path) {
  return type->canSel(path);
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
    ASSERT(0,"Cannot be here");
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


SelectPath& Wireable::getSelectPath() {
  if (selectpath.size()==0) {
    Wireable* top = this;
    while(auto s = dyn_cast<Select>(top)) {
      selectpath.push_front(s->getSelStr());
      top = s->getParent();
    }
    if (isa<Interface>(top))
      selectpath.push_front("self");
    else { //This should be an instance
      string instname = cast<Instance>(top)->getInstname();
      selectpath.push_front(instname);
    }
  }
  return selectpath;
}

Context* Wireable::getContext() {
  ASSERT(container != nullptr, this->toString() + " has null container");
  return container->getContext();
}
string Wireable::wireableKind2Str(WireableKind wb) {
  switch(wb) {
    case WK_Interface: return "Interface";
    case WK_Instance: return "Instance";
    case WK_Select: return "Select";
  }
  ASSERT(false,"Unknown WireableKind: " + to_string(wb));
}

namespace {
void traverse2(std::map<SelectPath,Wireable*>& ret, SelectPath path, Wireable* w) {
  ret.emplace(path,w);
  for (auto spair : w->getSelects()) {
    SelectPath newpath = path;
    path.push_back(spair.first);
    traverse2(ret,newpath,spair.second);
  }
}
}

std::map<SelectPath,Wireable*> Wireable::getAllSelects() {
  std::map<SelectPath,Wireable*> ret;
  SelectPath path;
  traverse2(ret,path,this);
  return ret;
}

namespace {
void traverse3(std::map<SelectPath,Wireable*>& ret, SelectPath path, Wireable* w) {
  if (!isa<Select>(w)) return;
  Select* select = cast<Select>(w);
  path.push_front(select->getSelStr());
  ret.emplace(path,select->getParent());
  traverse3(ret, path,select->getParent());
}

}

std::map<SelectPath,Wireable*> Wireable::getAllParents() {
  std::map<SelectPath,Wireable*> ret;
  SelectPath path;
  traverse3(ret,path,this);
  return ret;
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

string Interface::toString() const{
  return "self";
}



Instance::Instance(ModuleDef* container, string instname, Module* moduleRef, Values modargs) : Wireable(WK_Instance,container,nullptr), instname(instname), moduleRef(moduleRef) {
  checkStringSyntax(instname);
  //ASSERT(container->getInstances().count(instname)==0,"Cannot add two instances with the same name: " + instname);
  ASSERT(moduleRef,"Module is null, in inst: " + this->getInstname());
  //First merge default args
  mergeValues(modargs,moduleRef->getDefaultModArgs());
  //Check if modargs is the same as expected by ModuleRef
  checkValuesAreParams(modargs,moduleRef->getModParams(),instname);
  
  this->modargs = modargs;

  //TODO checkif instname is unique
  this->type = moduleRef->getType();
}

string Instance::toString() const {
  return instname;
}

void Instance::replace(Module* moduleRef, Values modargs) {
  ASSERT(moduleRef,"ModuleRef is null in inst: " + this->getInstname());
  ASSERT(this->getType()==moduleRef->getType(),"NYI, Cannot replace with a different type");
  this->moduleRef = moduleRef;
  this->modargs = modargs;
  checkValuesAreParams(modargs,moduleRef->getModParams(),this->getInstname());
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
