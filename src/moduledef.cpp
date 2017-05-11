
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
string ModuleDef::getName() {return module->getName();}
Type* ModuleDef::getType() {return module->getType();}

Instance* ModuleDef::addInstance(string instname,Generator* gen, Args genargs,Args config) {
  assert(instances.count(instname)==0);
  
  Instance* inst = new Instance(this,instname,gen,genargs,config);
  instances[instname] = inst;
  
  return inst;
}

Instance* ModuleDef::addInstance(string instname,Module* m,Args config) {
  Instance* inst = new Instance(this,instname,m,config);
  instances[instname] = inst;
  
  return inst;
}

Instance* ModuleDef::addInstance(Instance* i) {
  if( i->isGen()) 
    return addInstance(i->getInstname(),i->getGeneratorRef(),i->getGenargs(),i->getConfigArgs());
  else 
    return addInstance(i->getInstname(),i->getModuleRef(),i->getConfigArgs());
}


void ModuleDef::wire(Wireable* a, Wireable* b) {
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

void ModuleDef::wire(SelectPath pathA, SelectPath pathB) {
  this->wire(this->sel(pathA),this->sel(pathB));
}

void ModuleDef::wire(string pathA, string pathB) {
  this->wire(this->sel(pathA),this->sel(pathB));
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
    assert(instances.count(s) && "Cannot find instance!");
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


} //coreir namespace
