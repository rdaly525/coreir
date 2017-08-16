
#include "passmanager.h"
#include "coreir-passes/common.h"
#include <stack>


using namespace CoreIR;

PassManager::PassManager(Context* c) : c(c) {
  initializePasses(*this);
  
  //Give all the passes access to passmanager
  for (auto pmap : passMap) {
    pmap.second->addPassManager(this);
  }
  
  //this->instanceGraph = new InstanceGraph();
}

void PassManager::addPass(Pass* p) {
  ASSERT(passMap.count(p->name) == 0,"Cannot add duplicate \"" + p->name + "\" pass");
  passMap[p->name] = p;
  if (p->isAnalysis) {
    analysisPasses[p->name] = false;
  }
  //Setting the dependencies and such
  p->setAnalysisInfo();
}

//Only do Global for now TODO
bool PassManager::runNamespacePass(Pass* pass) {
  assert(pass);
  cout << "Running Pass! " << pass->getName() << endl;
  auto nspass = cast<NamespacePass>(pass);
  cout << "N: " << nspass->getName() << endl;
  Namespace* ns = this->c->getGlobal();
  cout << "global exists" << ns->getName() << endl;
  nspass->nstest();
  cout << "after test" << endl;
  return nspass->runOnNamespace(ns);
}
  
//bool PassManager::runNamespacePass(vector<Pass*>& passes) {
//  bool modified = false;
//  for (auto npass : passes) {
//    assert(isa<NamespacePass>(npass));
//    modified |= cast<NamespacePass>(npass)->runOnNamespace(this->ns);
//    modified |= npass->runFinalize();
//  }
//  if (modified) {
//    instanceGraphStale = true;
//  }
//  return modified;
//}


////This does do pipelineing
//bool PassManager::runModulePass(vector<Pass*>& passes) {
//  bool modified = false;
//  for (auto modmap : ns->getModules()) {
//    Module* m = modmap.second;
//    for (auto mpass : passes) {
//      assert(isa<ModulePass>(mpass));
//      modified |= cast<ModulePass>(mpass)->runOnModule(m);
//    }
//  }
//  for (auto mpass : passes) {
//    modified |= mpass->runFinalize();
//  }
//  return modified;
//}
//
//
////Does not do pipelineing
//bool PassManager::runInstanceGraphPass(vector<Pass*>& passes) {
//  
//  if (this->instanceGraphStale) {
//    instanceGraph->construct(ns);
//  }
//  
//  bool modified = false;
//  for (auto igpass : passes) {
//    assert(isa<InstanceGraphPass>(igpass));
//    for (auto node : this->instanceGraph->getSortedNodes()) {
//      modified |= cast<InstanceGraphPass>(igpass)->runOnInstanceGraphNode(*node);
//    }
//    modified |= igpass->runFinalize();
//  }
//  return modified;
//}

bool PassManager::run(PassOrder order) {
  bool ret = false;
  stack<string> work;
  for (auto oname : order) {
    ASSERT(passMap.count(oname),"Did not load pass: " + oname);
    work.push(oname);
    for (auto it = passMap[oname]->dependencies.rbegin(); it!=passMap[oname]->dependencies.rend(); ++it) {
      ASSERT(analysisPasses.count(*it),"Dependency \"" + *it + "\" for \"" + oname + "\" is not an analysis!");
      work.push(*it);
    }
    //Actually run the passes now
    while (!work.empty()) {
      string pname = work.top(); work.pop();
      bool anal = analysisPasses.count(pname) > 0;
      Pass* p = passMap[pname];
      
      //If it is an analysis and is not stale, do not run!
      if (anal && analysisPasses[pname]) {
        continue;
      }
      else if (anal) { //is analysis and needs to be run
        p->releaseMemory(); //clear data structures  
      }
      //Run it!
      bool modified = this->runPass(p);
      if (anal) {
        ASSERT(!modified,"Analysis pass cannot modify IR!");
        analysisPasses[pname] = true;
      }
      else if (modified) { //Not analysis
        //If it modified, need to conservatly invalidate all analysis passes
        for (auto amap : analysisPasses) {
          analysisPasses[amap.first] = false;
        }
      }
      ret |= modified;

    }
  }
  return ret;
}

bool PassManager::runPass(Pass* p) {
  switch(p->getKind()) {
    case Pass::PK_Namespace:
      return runNamespacePass(p);
    default:
      break;
  }
  ASSERT(0,"NYI");
}
  
PassManager::~PassManager() {
  for (auto p : passMap) {
    delete p.second;
  }
}

Pass::~Pass() {}
