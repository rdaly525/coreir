
#include "coreir/ir/passmanager.h"
#include "coreir/passes/common.h"
#include <stack>

#include "coreir/passes/analysis/createinstancegraph.h"
#include "coreir/passes/analysis/createinstancemap.h"



using namespace std;
using namespace CoreIR;


PassManager::PassManager(Context* c) : c(c) {
  initializePasses(*this);
  

  //Give all the passes access to passmanager
  for (auto pmap : passMap) {
    pmap.second->addPassManager(this);
  }

}


void PassManager::addPass(Pass* p) {
  p->addPassManager(this);
  ASSERT(passMap.count(p->name) == 0,"Cannot add duplicate \"" + p->name + "\" pass");
  passMap[p->name] = p;
  if (p->isAnalysis) {
    analysisPasses[p->name] = false;
  }
  //Setting the dependencies and such
  p->setAnalysisInfo();

  //Little hacky
  if (auto ivp = dyn_cast<InstanceVisitorPass>(p)) {
    ivp->setVisitorInfo();
  }

}

bool PassManager::runNamespacePass(Pass* pass) {
  bool modified = false;
  for (auto ns : this->nss) {
    modified |= cast<NamespacePass>(pass)->runOnNamespace(ns);
  }
  return modified;
}
bool PassManager::runContextPass(Pass* pass) {
  return cast<ContextPass>(pass)->runOnContext(c);
}

//Only runs on modules with definitions
bool PassManager::runModulePass(Pass* pass) {
  bool modified = false;
  ModulePass* mpass = cast<ModulePass>(pass);
  for (auto ns : this->nss) {
    for (auto modmap : ns->getModules()) {
      Module* m = modmap.second;
      if (m->hasDef()) {
        modified |= mpass->runOnModule(m);
      }
    }
  }
  return modified;
}

//Only runs on Instances
bool PassManager::runInstancePass(Pass* pass) {
  //Load up list of instances in case the pass changes the list
  //Turn this into a pass
  vector<Instance*> insts;
  for (auto ns : this->nss) {
    for (auto modmap : ns->getModules()) {
      if (!modmap.second->hasDef()) continue;
      for (auto instmap : modmap.second->getDef()->getInstances()) {
        insts.push_back(instmap.second);
      }
    }
  }
  InstancePass* ipass = cast<InstancePass>(pass);
  bool modified = false;
  for (auto inst : insts) {
    modified |= ipass->runOnInstance(inst);
  }
  return modified;
}

bool PassManager::runInstanceVisitorPass(Pass* pass) {

  //Get the analysis pass which constructs the instancegraph
  auto cfim = static_cast<Passes::CreateInstanceMap*>(this->getAnalysisPass("createfullinstancemap"));
  bool modified = false;
  InstanceVisitorPass* ivpass = cast<InstanceVisitorPass>(pass);
  for (auto imap : cfim->getModInstanceMap()) {
    modified |= ivpass->runOnModInstances(imap.first,imap.second);
  }
  for (auto imap : cfim->getGenInstanceMap()) {
    modified |= ivpass->runOnGenInstances(imap.first,imap.second);
  }
  return modified;
}

bool PassManager::runInstanceGraphPass(Pass* pass) {

  //Get the analysis pass which constructs the instancegraph
  auto cig = static_cast<Passes::CreateInstanceGraph*>(this->getAnalysisPass("createinstancegraph"));
  bool modified = false;
  InstanceGraphPass* igpass = cast<InstanceGraphPass>(pass);
  bool onlyTop = igpass->isOnlyTop();
  for (auto node : cig->getInstanceGraph()->getSortedNodes()) {
    if (!onlyTop || cig->getInstanceGraph()->validOnlyTop(node)) {
      modified |= igpass->runOnInstanceGraphNode(*node);
    }
  }
  return modified;
}

bool PassManager::runPass(Pass* p) {
  if (verbose) {
    cout << "Running Pass: " << p->getName() << endl;
  }
  bool modified = false;
  switch(p->getKind()) {
    case Pass::PK_Context:
      modified = runContextPass(p);
      break;
    case Pass::PK_Namespace:
      modified = runNamespacePass(p);
      break;
    case Pass::PK_Module:
      modified = runModulePass(p);
      break;
    case Pass::PK_Instance:
      modified = runInstancePass(p);
      break;
    case Pass::PK_InstanceVisitor:
      modified = runInstanceVisitorPass(p);
      break;
    case Pass::PK_InstanceGraph:
      modified = runInstanceGraphPass(p);
      break;
    default:
      ASSERT(0,"NYI!");
  }
  modified |= p->finalize();
  if (verbose) {
    p->print();
  }
  passLog.push_back(p->getName());
  return modified;
}

//TODO should check for circular dependencies
void PassManager::pushAllDependencies(string oname,stack<string> &work) {
  ASSERT(passMap.count(oname),"Can not run pass \"" + oname + "\" because it was never loaded!");
  work.push(oname);
  for (auto it = passMap[oname]->dependencies.rbegin(); it!=passMap[oname]->dependencies.rend(); ++it) {
    ASSERT(passMap.count(*it),"Dependency " + *it + " for " + oname + " Was never loaded!");
    ASSERT(analysisPasses.count(*it),"Dependency \"" + *it + "\" for \"" + oname + "\" cannot be a transform pass");
    pushAllDependencies(*it,work);
  }
}

bool PassManager::run(PassOrder order,vector<string> nsnames) {
  this->nss.clear();
  ASSERT(passMap.count("verifyinputconnections"),"Missing weak verifier pass");
  for (auto nsname : nsnames) {
    ASSERT(c->hasNamespace(nsname),"Missing namespace: " + nsname);
    this->nss.push_back(c->getNamespace(nsname));
  }
  //For now just do all namespaces
  //for (auto ns : c->getNamespaces()) {
  //  nss.push_back(ns.second);
  //}

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
        //Run Verifier pass
        this->runPass(passMap["verifyinputconnections"]);
        analysisPasses["verifyinputconnections"] = true;
      }
      ret |= modified;

    }
  }
  return ret;
}

void PassManager::printLog() {
  cout << "Ran the following passes:" << endl;
  for (auto p : passLog) {
    cout << "  " << p << endl;
  }
}
void PassManager::printPassChoices() {
  cout << "Analysis Passes" << endl;
  for (auto ap : analysisPasses) {
    cout << "  " << ap.first << endl;
  }
  cout << endl << "Transform Passes" << endl;
  for (auto p : passMap) {
    if (analysisPasses.count(p.first)==0) {
      cout << "  " << p.first << endl;
    }
  }
}



PassManager::~PassManager() {
  for (auto p : passMap) {
    delete p.second;
  }
}

Pass::~Pass() {}
