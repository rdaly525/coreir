#include "wireable.hpp"

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
  //Create new select
  Context* c = getContext();
  Type* ret = c->Any();
  Error e;
  bool error = type->sel(selStr,&ret,&e);
  if (error) {
    e.message("  Wireable: " + toString());
    e.fatal();
    getContext()->error(e);
  }
  
  Select* select = new Select(this->getContainer(),this,selStr, ret);
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
  unordered_set<Connection> uniqueCons;
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

//merge a1 into a0 
void mergeArgs(Args& a0, Args a1) {
  for (auto arg : a1) {
    if (a0.count(arg.first)==0) {
      a0.insert(arg);
    }
  }
}


Instance::Instance(ModuleDef* container, string instname, Module* moduleRef, Args configargs) : Wireable(WK_Instance,container,nullptr), instname(instname), moduleRef(moduleRef), isgen(false) {
  ASSERT(moduleRef,"Module is null, in inst: " + this->getInstname());
  //First merge default args
  mergeArgs(configargs,moduleRef->getDefaultConfigArgs());
  //Check if configargs is the same as expected by ModuleRef
  checkArgsAreParams(configargs,moduleRef->getConfigParams());
  this->configargs = configargs;
  
  //TODO checkif instname is unique
  this->type = moduleRef->getType();
}

Instance::Instance(ModuleDef* container, string instname, Generator* generatorRef, Args genargs, Args configargs) : Wireable(WK_Instance,container,nullptr), instname(instname), isgen(true), generatorRef(generatorRef) {
  ASSERT(generatorRef,"Generator is null, in inst: " + this->getInstname());
  mergeArgs(genargs,generatorRef->getDefaultGenArgs());
  checkArgsAreParams(genargs,generatorRef->getGenParams());
  this->genargs = genargs;
  this->type = generatorRef->getTypeGen()->getType(genargs);
  mergeArgs(configargs,generatorRef->getDefaultConfigArgs());
  checkArgsAreParams(configargs,generatorRef->getConfigParams());
  this->configargs = configargs;
}

string Interface::toString() const{
  return "self";
}

string Instance::toString() const {
  return instname;
}

//TODO this could throw an error. Bad!
Arg* Instance::getConfigArg(string s) { 
  ASSERT(configargs.count(s)>0, "ConfigArgs does not contain field: " + s);
  return configargs.at(s);
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

void Instance::replace(Module* moduleRef, Args configargs) {
  ASSERT(!this->isGen(),"NYI, Cannot replace a generator instance with a module isntance")
  ASSERT(this->getType()==moduleRef->getType(),"NYI, Cannot replace with a different type")
  ASSERT(moduleRef,"ModuleRef is null in inst: " + this->getInstname());
  this->moduleRef = moduleRef;
  this->configargs = configargs;
  checkArgsAreParams(configargs,moduleRef->getConfigParams());
}

//TODO this is probably super unsafe and will leak memory
//TODO I do not think this deals with default args
void Instance::replace(Generator* generatorRef, Args genargs, Args configargs) {
  ASSERT(generatorRef,"Generator is null! in inst: " + this->getInstname());
  ASSERT(this->isGen(),"NYI, Cannot replace a generator instance with a module isntance");
  
  this->generatorRef = generatorRef;
  this->genargs = genargs;
  Type* newType = generatorRef->getTypeGen()->getType(genargs);
  ASSERT(this->getType() == newType,"NYI, Cannot replace with a different type");

  this->configargs = configargs;

  checkArgsAreParams(configargs,generatorRef->getConfigParams());
  checkArgsAreParams(genargs,generatorRef->getGenParams());

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
