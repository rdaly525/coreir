#include "moduledef.hpp"

using namespace std;

namespace CoreIR {


ModuleDef* Module::newModuleDef() {
  
  ModuleDef* md = new ModuleDef(this);
  mdefList.push_back(md);
  return md;
}

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
    cout << "      " << inst.first << " : " << inst.second->getInstRef()->getName() << endl;
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
  //Should this type be resolved? Just create a typeGenInst for now
  Context* c = gen->getContext();
  Type* type = gen->getTypeGen().fun(c,genargs);
  
  Instance* inst = new Instance(this,instname,gen,type,genargs,config);
  instances[instname] = inst;
  
  return inst;
}

Instance* ModuleDef::addInstance(string instname,Module* m,Args config) {
  Instance* inst = new Instance(this,instname,m,m->getType(),Args(),config);
  instances[instname] = inst;
  
  return inst;
}

Instance* ModuleDef::addInstance(Instance* i) {
  if( i->getInstRef()->isKind(MOD)) 
    return addInstance(i->getInstname(),(Module*) i->getInstRef(),i->getConfig());
  else 
    return addInstance(i->getInstname(),(Generator*) i->getInstRef(),i->getConfig(),i->getArgs());
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

void ModuleDef::wire(WirePath pathA, WirePath pathB) {
  Wireable* curA = this->sel(pathA.first);
  Wireable* curB = this->sel(pathB.first);
  for (auto str : pathA.second) curA = curA->sel(str);
  for (auto str : pathB.second) curB = curB->sel(str);
  this->wire(curA,curB);
}


Wireable* ModuleDef::sel(string s) { 
  if (s=="self") return interface;
  else return instances[s]; 
}


} //coreir namespace
