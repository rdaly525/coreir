
#include "moduledef.hpp"
#include "typegen.hpp"
#include <iterator>

using namespace std;

namespace CoreIR {



ModuleDef::ModuleDef(Module* module) : module(module) {
  interface = new Interface(this,module->getContext()->Flip(module->getType()));
  cache = new SelCache();
}

ModuleDef::~ModuleDef() {
  //Delete interface, instances, cache
  delete interface;
  for(auto inst : instances) delete inst.second;
  delete cache;
}


void ModuleDef::print(void) {
  cout << "  Def:" << endl;
  cout << "    Instances:" << endl;
  for (auto inst : instances) {
    cout << "      " << inst.first << " : " << inst.second->getModuleRef()->getName() << endl;
  }
  cout << "    Connections:\n";
  for (auto connection : connections) {
    cout << "      " << *(connection.first) << " <=> " << *(connection.second) << endl ;
  }
  cout << endl;
}

Context* ModuleDef::getContext() { return module->getContext(); }
const string& ModuleDef::getName() {return module->getName();}
Type* ModuleDef::getType() {return module->getType();}

ModuleDef* ModuleDef::copy() {
  Module* m = this->getModule();
  ModuleDef* def = m->newModuleDef();
  for (auto inst : this->getInstances()) {
    def->addInstance(inst.second);
  }

  for (auto con: this->getConnections()) {
    SelectPath a = con.first->getSelectPath();  
    SelectPath b = con.second->getSelectPath();
    def->connect(a,b);
  }
  return def;
}



//Can pass in either a single instance name
//Or pass in a '.' deleminated string
Wireable* ModuleDef::sel(string s) { 
  if (hasChar(s,'.')) {
    SelectPath path = splitString(s,'.');
    return this->sel(path);
  }
  if (s=="self") return interface;
  else {
    ASSERT(instances.count(s),"Cannot find instance " + s);
    return instances[s]; 
  }
}

Wireable* ModuleDef::sel(SelectPath path) {
  Wireable* cur = this->sel(path[0]);
  for (auto it = std::next(path.begin()); it != path.end(); ++it) {
    cur = cur->sel(*it);
  }
  return cur;
}


Instance* ModuleDef::addInstance(string instname,Generator* gen, Args genargs,Args config) {
  assert(instances.count(instname)==0);
  
  Instance* inst = new Instance(this,instname,gen,genargs,config);
  instances[instname] = inst;

  //Add to instanceMap
  instanceMap[gen].insert(inst);

  return inst;
}

Instance* ModuleDef::addInstance(string instname,Module* m,Args config) {
  Instance* inst = new Instance(this,instname,m,config);
  instances[instname] = inst;
  
  //Add to instanceMap
  instanceMap[m].insert(inst);
  
  return inst;
}

Instance* ModuleDef::addInstance(Instance* i,string iname) {
  if (iname=="") {
    iname = i->getInstname();
  }
  if( i->isGen()) 
    return addInstance(iname,i->getGeneratorRef(),i->getGenargs(),i->getConfigArgs());
  else 
    return addInstance(iname,i->getModuleRef(),i->getConfigArgs());
}


void ModuleDef::connect(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same context
  Context* c = getContext();
  if (a->getModuleDef()!=this || b->getModuleDef() != this) {
    Error e;
    e.message("connections can only occur within the same module");
    e.message("  This ModuleDef: " + module->getName());
    e.message("  ModuleDef of " + a->toString() + ": " + a->getModuleDef()->getName());
    e.message("  ModuleDef of " + b->toString() + ": " + b->getModuleDef()->getName());
    c->error(e);
    return;
  }

  // TODO should I type check here at all?
  //checkWiring(a,b);
  
  //minmax gauranees an ordering
  auto sorted = std::minmax(a,b);
  Connection connect(sorted.first,sorted.second);
  if (!connections.count(connect)) {
    
    //Update 'a' and 'b'
    a->addConnectedWireable(b);
    b->addConnectedWireable(a);
    connections.insert(connect);
  }
  else {
    cout << "ALREADY ADDED CONNECTION!" << endl;
  }
}

void ModuleDef::connect(SelectPath pathA, SelectPath pathB) {
  this->connect(this->sel(pathA),this->sel(pathB));
}

void ModuleDef::connect(string pathA, string pathB) {
  this->connect(this->sel(pathA),this->sel(pathB));
}
void ModuleDef::connect(std::initializer_list<const char*> pA, std::initializer_list<const char*> pB) {
  connect(SelectPath(pA.begin(),pA.end()),SelectPath(pB.begin(),pB.end()));
}
void ModuleDef::connect(std::initializer_list<std::string> pA, std::initializer_list<string> pB) {
  connect(SelectPath(pA.begin(),pA.end()),SelectPath(pB.begin(),pB.end()));
}

//This will remove all connections from a specific wireable
void ModuleDef::disconnect(Wireable* w) {
  for (auto wc : w->getConnectedWireables()) {
    this->disconnect(w,wc);
  }
}

void ModuleDef::disconnect(Wireable* a, Wireable* b) {
  //First check if this exists in the list of connections
  auto sorted = std::minmax(a,b);
  Connection connect(sorted.first,sorted.second);
  if (connections.count(connect)==0) {
    assert("Connection does not exist! Not removing");
    return;
  }
  
  //remove reference from a and 
  a->removeConnectedWireable(b);
  b->removeConnectedWireable(a);

  //Delete connection from list
  connections.erase(connect);
}

void disconnectAllWireables(ModuleDef* m, Wireable* w) {
  for (auto sels : w->getSelects()) {
    disconnectAllWireables(m,sels.second);
  }
  m->disconnect(w);
}
void ModuleDef::removeInstance(Instance* inst) {
  removeInstance(inst->getInstname());
}

void ModuleDef::removeInstance(string iname) {
  //First verify that instance exists
  ASSERT(instances.count(iname), "Instance " + iname + " does not exist");
  Instance* inst = instances.at(iname);
  
  //First remove all the connections from this instance
  disconnectAllWireables(this,inst);

  //Now remove this instance
  instances.erase(iname);
  
  //Remove this from the instanceMap
  Instantiable* i;
  if (inst->isGen()) {
    i = inst->getGeneratorRef();
  }
  else {
    i = inst->getModuleRef();
  }
  assert(instanceMap.count(i)>0);
  assert(instanceMap[i].count(inst)>0);
  instanceMap[i].erase(inst);

}

} //coreir namespace
