
#include "passmanager.h"
#include "coreir-passes/common.h"
#include <stack>

#include "coreir-passes/analysis/constructinstancegraph.h"



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
  cout << "adding Pass: " + p->getName() << endl;
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
  return cast<NamespacePass>(pass)->runOnNamespace(this->c->getGlobal());
}

//Only do Global for now TODO
bool PassManager::runModulePass(Pass* pass) {
  bool modified = false;
  ModulePass* mpass = cast<ModulePass>(pass);
  for (auto modmap : c->getGlobal()->getModules()) {
    Module* m = modmap.second;
    modified |= mpass->runOnModule(m);
  }
  return modified;
}


bool PassManager::runInstanceGraphPass(Pass* pass) {
  
  //Get the analysis pass which constructs the instancegraph
  auto cig = static_cast<Passes::ConstructInstanceGraph*>(this->getAnalysisPass("constructInstanceGraph"));
  bool ret = false;
  InstanceGraphPass* igpass = cast<InstanceGraphPass>(pass);
  for (auto node : cig->getInstanceGraph()->getSortedNodes()) {
    bool modified = igpass->runOnInstanceGraphNode(*node);
    ret |= modified;
  }
  return ret;
}

bool PassManager::runPass(Pass* p) {
  switch(p->getKind()) {
    case Pass::PK_Namespace:
      return runNamespacePass(p);
    case Pass::PK_Module:
      return runModulePass(p);
    case Pass::PK_InstanceGraph:
      return runInstanceGraphPass(p);
    default:
      break;
  }
  ASSERT(0,"NYI");
}

//TODO should check for circular dependencies
void PassManager::pushAllDependencies(string oname,stack<string> &work) {
  ASSERT(passMap.count(oname),"Can not run pass \"" + oname + "\" because it was never loaded!");
  work.push(oname);
  for (auto it = passMap[oname]->dependencies.rbegin(); it!=passMap[oname]->dependencies.rend(); ++it) {
    ASSERT(analysisPasses.count(*it),"Dependency \"" + *it + "\" for \"" + oname + "\" cannot be a transform pass");
    pushAllDependencies(*it,work);
  }  
}

bool PassManager::run(PassOrder order) {
  bool ret = false;
  //Execute each in order (and the respective dependencies) independently
  for (auto oname : order) {
    stack<string> work;
    pushAllDependencies(oname,work);
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


  
PassManager::~PassManager() {
  for (auto p : passMap) {
    delete p.second;
  }
}

Pass::~Pass() {}
