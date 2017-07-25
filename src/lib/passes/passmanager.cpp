
#include "coreir-pass/passmanager.h"

using namespace CoreIR;

void PassManager::addPass(Pass* p, uint ordering) {
  if (passOrdering.count(ordering)==0) {
    passOrdering[ordering] = unordered_map<uint,vector<Pass*>>();
  }
  passOrdering[ordering][p->getKind()].push_back(p);
}

//This does do pipelineing
bool PassManager::runModulePass(vector<Pass*>& passes) {
  bool modified = false;
  for (auto modmap : ns->getModules()) {
    string s = modmap.first;
    Module* m = modmap.second;
    for (auto mpass : passes) {
      assert(isa<ModulePass>(mpass));
      modified |= cast<ModulePass>(mpass)->runOnModule(m);
    }
  }
  return modified;
  
}


//Does not do pipelineing
bool PassManager::runInstanceGraphPass(vector<Pass*>& passes) {
  bool modified = false;
  for (auto igpass : passes) {
    assert(isa<InstanceGraphPass>(igpass));
    for (auto node : this->instanceGraph.getSortedNodes()) {
      modified |= cast<InstanceGraphPass>(igpass)->runOnInstanceGraphNode(*node);
    }
  }
  return modified;
}

bool PassManager::run() {
  //For now I have to do only the modules.
  bool modified = false;
  for (auto passOrders : passOrdering) {
    uint idx = passOrders.first;
    cout << "OrderIdx " << idx << endl;
    //Do modulePasses first
    if (passOrders.second.count(Pass::PK_Module)>0) {
      modified |= runModulePass(passOrders.second[Pass::PK_Module]);
    }
    if (passOrders.second.count(Pass::PK_InstanceGraph)>0) {
      modified |= runInstanceGraphPass(passOrders.second[Pass::PK_Module]);
    }

  
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



