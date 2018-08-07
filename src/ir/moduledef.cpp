#include "coreir/ir/moduledef.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/common.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/types.h"
#include "coreir/ir/error.h"
#include "coreir/ir/value.h"
#include <iterator>


using namespace std;

namespace CoreIR {

ModuleDef::ModuleDef(Module* module) : module(module), instancesIterFirst(nullptr), instancesIterLast(nullptr) {
  interface = new Interface(this,cast<RecordType>(module->getType()->getFlipped()));
}

ModuleDef::~ModuleDef() {
  //Delete interface, instances, cache
  delete interface;
  for(auto inst : instances) delete inst.second;
}


void ModuleDef::print(void) {
  cout << "  Def:" << endl;
  cout << "    Instances:" << endl;
  for (auto inst : this->getInstances()) {
    Module* mref = inst.second->getModuleRef();
    if (mref->isGenerated()) {
      cout << "      " << inst.first << " : " << mref->getGenerator()->getName() << ::CoreIR::toString(mref->getGenArgs()) << endl;
    }
    else {
      cout << "      " << inst.first << " : " << mref->getName() << endl;
    }
  }
  cout << "    Connections:\n";
  for (auto connection : connections) {
    cout << "      " << toString(connection) << endl;
  }
  cout << endl;
}

Context* ModuleDef::getContext() { return module->getContext(); }
const string& ModuleDef::getName() {return module->getName();}
RecordType* ModuleDef::getType() {return module->getType();}

  void addCorrespondingSelects(Wireable* const original,
                               Wireable* const cpy,
                               std::map<Wireable*, Wireable*>& origToCopies) {
    origToCopies[original] = cpy;
    for (auto sel : original->getSelects()) {
      addCorrespondingSelects(sel.second, cpy->sel(sel.first), origToCopies);
    }
  }

ModuleDef* ModuleDef::copy() {
  Module* m = this->getModule();
  ModuleDef* def = m->newModuleDef();

  map<Wireable*, Wireable*> oldWireablesToCopies;
  
  for (auto inst : this->getInstances()) {
    def->addInstance(inst.second);
  }

  for (auto con: this->getConnections()) {

    const SelectPath& a = con.first->getSelectPath();
    const SelectPath& b = con.second->getSelectPath();
    def->connect(a,b);

  }

  return def;
}

bool ModuleDef::canSel(const std::string& selstr) {
  SelectPath path = splitString<SelectPath>(selstr,'.');
  return this->canSel(path);
}
bool ModuleDef::canSel(SelectPath path) {
  string iname = path[0];
  Wireable* inst;
  if (iname=="self") {
    inst = this->interface;
  }
  else {
    if (this->instances.count(iname)==0) return false;
    inst = this->instances[iname];
  }
  path.pop_front();
  return inst->canSel(path);
}


//Can pass in either a single instance name
//Or pass in a '.' deleminated string
Wireable* ModuleDef::sel(const string& s) { 
  if (hasChar(s,'.')) {
    SelectPath path = splitString<SelectPath>(s,'.');
    return this->sel(path);
  }
  if (s=="self") return interface;
  else {
    ASSERT(instances.count(s),"Cannot find instance " + s);
    return instances[s]; 
  }
}

Wireable* ModuleDef::sel(const SelectPath& path) {
  Wireable* cur = this->sel(path[0]);
  for (auto it = std::next(path.begin()); it != path.end(); ++it) {
    cur = cur->sel(*it);
  }
  return cur;
}
Wireable* ModuleDef::sel(std::initializer_list<const char*> path) {
  return sel(SelectPath(path.begin(),path.end()));
}
Wireable* ModuleDef::sel(std::initializer_list<std::string> path) {
  return sel(SelectPath(path.begin(),path.end()));
}

void ModuleDef::appendInstanceToIter(Instance* instance) {
    if (instancesIterFirst == nullptr) {
        assert(this->instancesIterLast == nullptr);
        // Sets `instance` to the current first and last pointer of the
        // iterator and sets the prev and next pointers to be null
        this->instancesIterFirst = instance;
        this->instancesIterLast = instance;
        this->instancesIterNextMap[instance] = nullptr;
        this->instancesIterPrevMap[instance] = nullptr;
    } else {
        assert(this->instancesIterLast != nullptr);
        Instance* currLast = this->instancesIterLast;
        // Updates the current last instance's next to point to the new instance,
        assert(this->instancesIterNextMap[currLast] == nullptr);  // current last shouldn't have a next
        this->instancesIterNextMap[currLast] = instance;
        // Sets the new instance's prev to point the current last instance,
        this->instancesIterPrevMap[instance] = currLast;
        // Sets the new instance's next to be null
        this->instancesIterNextMap[instance] = nullptr;
        // Sets the current last instance to be the new instance
        this->instancesIterLast = instance;
    }
}

void ModuleDef::removeInstanceFromIter(Instance* instance) {
    assert(this->instancesIterNextMap.count(instance) == 1);
    assert(this->instancesIterPrevMap.count(instance) == 1);
    // Because we set prev and next to be nullptr for the first and last, we
    // can assume the prev and next exist or are null
    Instance *next = this->instancesIterNextMap[instance];
    Instance *prev = this->instancesIterPrevMap[instance];
    // Update pointers to skip instance
    this->instancesIterNextMap[prev] = next;
    this->instancesIterPrevMap[next] = prev;
    if (instance == this->instancesIterLast) {
        // The new last is this instance's prev
        this->instancesIterLast = prev;
    }
    if (instance == this->instancesIterFirst) {
        // The new first is the this instance's next
        this->instancesIterFirst = next;
    }
}

Instance* ModuleDef::getInstancesIterNext(Instance* instance) {
    ASSERT(instance, "Cannot get next of IterEnd");
    ASSERT(this->instancesIterNextMap.count(instance) == 1, "DEBUG ME: instance not in iter"); // TODO: Should be an error?
    return this->instancesIterNextMap[instance];
}


 //   Instance(ModuleDef* container, std::string instname, Module* moduleRef, Values modargs);
Instance* ModuleDef::addInstance(string instname,Generator* gen, Values genargs,Values modargs) {
  ASSERT(instances.count(instname)==0,instname + " already an instance");

  Instance* inst = new Instance(this,instname,gen->getModule(genargs),modargs);
  instances[instname] = inst;

  appendInstanceToIter(inst);

  return inst;
}

Instance* ModuleDef::addInstance(string instname,Module* m,Values modargs) {
  ASSERT(instances.count(instname)==0,instname + " already an instance");
  Instance* inst = new Instance(this,instname,m,modargs);
  instances[instname] = inst;
  
  appendInstanceToIter(inst);
  
  return inst;
}

Instance* ModuleDef::addInstance(string instname,string iref,Values genOrModargs, Values modargs) {
  vector<string> split = splitRef(iref);
  GlobalValue* ref = this->getContext()->getGlobalValue(iref);
  if (auto g = dyn_cast<Generator>(ref)) {
    return this->addInstance(instname,g,genOrModargs,modargs);
  }
  else {
    auto m = cast<Module>(ref);
    return this->addInstance(instname,m,genOrModargs);
  }
}

Instance* ModuleDef::addInstance(Instance* i,string iname) {
  if (iname=="") {
    iname = i->getInstname();
  }
  Module* mref = i->getModuleRef();
  if(mref->isGenerated()) {
    return addInstance(iname,mref->getGenerator(),mref->getGenArgs(),i->getModArgs());
  }
  else {
    return addInstance(iname,i->getModuleRef(),i->getModArgs());
  }
}

void ModuleDef::connect(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same context
  Context* c = getContext();

  if (a->getContainer()!=this || b->getContainer() != this) {
    Error e;
    e.message("connections can only occur within the same module");
    e.message("  This ModuleDef: " + module->getName());
    e.message("  ModuleDef of " + a->toString() + ": " + a->getContainer()->getName());
    e.message("  ModuleDef of " + b->toString() + ": " + b->getContainer()->getName());
    c->error(e);
    return;
  }

  // TODO should I type check here at all?
  bool err = checkTypes(a,b);
  if (err) {
    c->die();
  }
  //checkWiring(a,b);
  
  Connection connect = connectionCtor(a,b);
  if (!connections.count(connect)) {
    
    //Update 'a' and 'b'
    a->addConnectedWireable(b);
    b->addConnectedWireable(a);
    connections.insert(connect);
  }
  else {
    ASSERT(0,"Trying to add following connection twice! " + toString(connect));
  }
}

void ModuleDef::connect(const SelectPath& pathA, const SelectPath& pathB) {
  this->connect(this->sel(pathA),this->sel(pathB));
}

void ModuleDef::connect(const string& pathA, const string& pathB) {
  this->connect(this->sel(pathA),this->sel(pathB));
}
void ModuleDef::connect(std::initializer_list<const char*> pA, std::initializer_list<const char*> pB) {
  connect(SelectPath(pA.begin(),pA.end()),SelectPath(pB.begin(),pB.end()));
}
void ModuleDef::connect(std::initializer_list<std::string> pA, std::initializer_list<string> pB) {
  connect(SelectPath(pA.begin(),pA.end()),SelectPath(pB.begin(),pB.end()));
}
bool ModuleDef::hasConnection(Wireable* a, Wireable* b) {
  Connection con = connectionCtor(a,b);
  return connections.count(con) > 0;
}

Connection ModuleDef::getConnection(Wireable* a, Wireable* b) {
  Connection con = connectionCtor(a,b);
  ASSERT(connections.count(con)>0,"Could not find connection!");
  
  return *connections.find(con);
}

//This will remove all connections from a specific wireable
void ModuleDef::disconnect(Wireable* w) {
  vector<Wireable*> toDelete;
  for (auto wc : w->getConnectedWireables()) {
    toDelete.push_back(wc);
  }
  for (auto wc : toDelete) {
    this->disconnect(w,wc);
  }
}

void ModuleDef::disconnect(Wireable* a, Wireable* b) {
  Connection connect = connectionCtor(a,b);
  this->disconnect(connect);
}
void ModuleDef::disconnect(Connection fstCon) {
  auto con = connectionCtor(fstCon.first, fstCon.second);
  
  if (connections.count(con) == 0) {
    cout << "All connections" << endl;
    for (auto conn : getConnections()) {
      cout << "\t" << toString(conn) << endl;
    }

    cout << "Contains reverse connection ? " << connections.count({con.second, con.first}) << endl;
  }

  ASSERT(connections.count(con),"Cannot delete connection that is not connected! " + toString(con));
  
  //remove references
  con.first->removeConnectedWireable(con.second);
  con.second->removeConnectedWireable(con.first);

  //Delete connection from list
  connections.erase(con);
}


void ModuleDef::removeInstance(Instance* inst) {
  removeInstance(inst->getInstname());
}


void ModuleDef::removeInstance(string iname) {
  //First verify that instance exists
  ASSERT(instances.count(iname), "Instance " + iname + " does not exist");
  Instance* inst = instances.at(iname);
  
  //First remove all the connections from this instance
  inst->disconnectAll();

  //remove the wireable (WILL free pointer)
  vector<string> sels;
  for (auto selmap : inst->getSelects()) {
    sels.push_back(selmap.first);
  }
  for (auto sel : sels) {
    inst->removeSel(sel);
  }

  //Now remove this instance
  instances.erase(iname);
  
  removeInstanceFromIter(inst);

  delete inst;
}

} //coreir namespace
