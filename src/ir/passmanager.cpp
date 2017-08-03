
#include "passmanager.h"

using namespace CoreIR;

PassManager::PassManager(Namespace* ns) : ns(ns) {
  this->instanceGraph = new InstanceGraph();
}

void PassManager::addPass(Pass* p, uint ordering) {
  if (passOrdering.count(ordering)==0) {
    passOrdering[ordering] = unordered_map<uint,vector<Pass*>>();
  }
  passOrdering[ordering][p->getKind()].push_back(p);
}


//This does do pipelineing (Only one namespace!)
bool PassManager::runNamespacePass(vector<Pass*>& passes) {
  bool modified = false;
  for (auto npass : passes) {
    assert(isa<NamespacePass>(npass));
    modified |= cast<NamespacePass>(npass)->runOnNamespace(this->ns);
    npass->print();
  }
  if (modified) {
    instanceGraphStale = true;
  }
  return modified;
}

//This does do pipelineing
bool PassManager::runModulePass(vector<Pass*>& passes) {
  bool modified = false;
  for (auto modmap : ns->getModules()) {
    Module* m = modmap.second;
    for (auto mpass : passes) {
      assert(isa<ModulePass>(mpass));
      modified |= cast<ModulePass>(mpass)->runOnModule(m);
      mpass->print();
    }
  }
  return modified;
}


//Does not do pipelineing
bool PassManager::runInstanceGraphPass(vector<Pass*>& passes) {
  
  if (this->instanceGraphStale) {
    instanceGraph->construct(ns);
  }
  
  bool modified = false;
  for (auto igpass : passes) {
    assert(isa<InstanceGraphPass>(igpass));
    for (auto node : this->instanceGraph->getSortedNodes()) {
      modified |= cast<InstanceGraphPass>(igpass)->runOnInstanceGraphNode(*node);
    }
    igpass->print();
  }
  return modified;
}

//This will clear all the passes
void PassManager::clear() {
  this->~PassManager();
  passOrdering.clear();
}

bool PassManager::run() {
  //For now I have to do only the modules.
  bool modified = false;
  for (auto passOrders : passOrdering) {
    //Do modulePasses first
    if (passOrders.second.count(Pass::PK_Namespace)>0) {
      modified |= runNamespacePass(passOrders.second[Pass::PK_Namespace]);
    }
    if (passOrders.second.count(Pass::PK_Module)>0) {
      modified |= runModulePass(passOrders.second[Pass::PK_Module]);
    }
    if (passOrders.second.count(Pass::PK_InstanceGraph)>0) {
      modified |= runInstanceGraphPass(passOrders.second[Pass::PK_InstanceGraph]);
    }
    cout << "Finished Running " << passOrders.first << endl;
  }
  return modified;
}



PassManager::~PassManager() {
  for (auto passOrders : passOrdering) {
    for (auto pmap : passOrders.second) {
      for (auto p : pmap.second) {
        delete p;
      }
    }
  }
}

Pass::~Pass() {}



