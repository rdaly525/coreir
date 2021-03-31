#include "coreir/ir/passmanager.h"
#include <stack>
#include "coreir/common/logging_lite.hpp"
#include "coreir/ir/coreir_symbol_table.hpp"
#include "coreir/passes/analysis/createinstancegraph.h"
#include "coreir/passes/analysis/createinstancemap.h"
#include "coreir/passes/common.h"

using namespace CoreIR;

PassManager::PassManager(Context* c)
    : c(c), symbolTable(new CoreIRSymbolTable()) {
  initializePasses(*this);

  // Give all the passes access to passmanager
  for (auto pmap : passMap) { pmap.second->addPassManager(this); }
}

void PassManager::addPass(Pass* p) {
  p->addPassManager(this);
  ASSERT(
    passMap.count(p->name) == 0,
    "Cannot add duplicate \"" + p->name + "\" pass");
  passMap[p->name] = p;
  // Setting the dependencies and such
  p->setAnalysisInfo();

  // Little hacky
  if (auto ivp = dyn_cast<InstanceVisitorPass>(p)) { ivp->setVisitorInfo(); }
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

// Only runs on modules with definitions
bool PassManager::runModulePass(Pass* pass) {
  bool modified = false;
  ModulePass* mpass = cast<ModulePass>(pass);
  std::map<Namespace*, std::map<std::string, Module*>> modMap;
  // create static list of modules in case new modules are added in the pass
  for (auto ns : this->nss) { modMap[ns] = ns->getModules(); }

  for (auto const& [_, modules] : modMap) {
    UNUSED(_);
    for (auto const& [_, m] : modules) {
      UNUSED(_);
      if (m->hasDef()) { modified |= mpass->runOnModule(m); }
    }
  }
  return modified;
}

// Only runs on Instances
bool PassManager::runInstancePass(Pass* pass) {
  // Load up list of instances in case the pass changes the list
  // Turn this into a pass
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
  for (auto inst : insts) { modified |= ipass->runOnInstance(inst); }
  return modified;
}

bool PassManager::runInstanceVisitorPass(Pass* pass) {

  // Get the analysis pass which constructs the instancegraph
  auto cfim = static_cast<Passes::CreateInstanceMap*>(
    this->getAnalysisPass("createfullinstancemap"));
  bool modified = false;
  InstanceVisitorPass* ivpass = cast<InstanceVisitorPass>(pass);
  for (auto imap : cfim->getModInstanceMap()) {
    modified |= ivpass->runOnModInstances(imap.first, imap.second);
  }
  for (auto imap : cfim->getGenInstanceMap()) {
    modified |= ivpass->runOnGenInstances(imap.first, imap.second);
  }
  return modified;
}

bool PassManager::runInstanceGraphPass(Pass* pass) {

  // Get the analysis pass which constructs the instancegraph
  auto cig = static_cast<Passes::CreateInstanceGraph*>(
    this->getAnalysisPass("createinstancegraph"));
  bool modified = false;
  InstanceGraphPass* igpass = cast<InstanceGraphPass>(pass);
  std::vector<Module*> mods;
  igpass->getModules(mods);
  for (auto node : cig->getInstanceGraph()->getFilteredNodes(mods)) {
    modified |= igpass->runOnInstanceGraphNode(*node);
  }
  return modified;
}

bool PassManager::runPass(Pass* p, vector<string>& pArgs) {
  LOG(DEBUG) << "Running Pass: " << p->getName();
  // Translate vector<string> into argc and argv
  int argc = pArgs.size();
  std::vector<char*> argv(argc);
  for (int i = 0; i < argc; ++i) {
    argv[i] = const_cast<char*>(pArgs[i].c_str());
  }
  if (argc > 1) { p->initialize(argc, &argv[0]); }
  bool modified = false;
  switch (p->getKind()) {
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
    ASSERT(0, "NYI!");
  }
  modified |= p->finalize();
  p->print();
  passLog.push_back(p->getName());
  return modified;
}

// TODO should check for circular dependencies
// pass can have args "mypass -blag -sdf"
void PassManager::pushAllDependencies(string passString, stack<string>& work) {
  vector<string> pArgs = splitStringByWhitespace(passString);
  string passName = pArgs[0];
  ASSERT(
    passMap.count(passName),
    "Can not run pass \"" + passName + "\" because it was never loaded!");
  work.push(passString);
  for (auto it = passMap[passName]->dependencies.rbegin();
       it != passMap[passName]->dependencies.rend();
       ++it) {
    string depPass = *it;  // Contains args
    vector<string> dpArgs = splitStringByWhitespace(depPass);
    string dpName = dpArgs[0];
    ASSERT(
      passMap.count(dpName),
      "Dependency " + depPass + " for " + passName + " Was never loaded!");
    ASSERT(
      passMap[dpName]->isAnalysis,
      "Dependency \"" + depPass + "\" for \"" + passName +
        "\" cannot be a transform pass");
    pushAllDependencies(depPass, work);
  }
}

// passes contains "passname -arg1 -arg2"
bool PassManager::run(vector<string>& passes, vector<string> nsnames) {
  this->nss.clear();
  for (auto nsname : nsnames) {
    ASSERT(c->hasNamespace(nsname), "Missing namespace: " + nsname);
    this->nss.push_back(c->getNamespace(nsname));
  }
  vector<vector<string>> passesParsed;
  for (auto p : passes) { passesParsed.push_back(splitStringByWhitespace(p)); }
  bool ret = false;
  // Execute each in order (and the respective dependencies) independently
  for (auto pass : passes) {
    stack<string> work;
    pushAllDependencies(pass, work);
    // Actually run the passes now
    while (!work.empty()) {
      string passString = work.top();
      work.pop();
      vector<string> pArgs = splitStringByWhitespace(passString);
      string pname = pArgs[0];

      Pass* p = passMap[pname];
      bool anal = p->isAnalysis;

      // If it is an analysis and is not stale, do not run!
      if (
        anal && analysisPasses.count(passString) &&
        analysisPasses[passString]) {
        continue;
      }
      else if (anal) {       // is analysis and needs to be run
        p->releaseMemory();  // clear data structures
      }
      // Run it!
      bool modified = this->runPass(p, pArgs);
      if (anal) {
        ASSERT(!modified, "Analysis pass cannot modify IR!");
        analysisPasses[passString] = true;
      }
      else if (modified) {  // Not analysis
        // If it modified, need to conservatly invalidate all analysis passes
        for (auto amap : analysisPasses) { analysisPasses[amap.first] = false; }
        // Run Verifier pass
        vector<string> verArgs = {"verifyinputconnections"};
        this->runPass(passMap["verifyinputconnections"], verArgs);
        analysisPasses["verifyinputconnections"] = true;
      }
      ret |= modified;
    }
  }
  return ret;
}
bool PassManager::isAnalysisCached(string pass) {
  ASSERT(analysisPasses.count(pass), pass + " was never loaded");
  return analysisPasses.at(pass);
}

void PassManager::printLog() {
  LOG(DEBUG) << "Ran the following passes:";
  for (auto p : passLog) { LOG(DEBUG) << "  " << p; }
}
void PassManager::printPassChoices() {
  LOG(DEBUG) << "Analysis Passes";
  for (auto ap : analysisPasses) { LOG(DEBUG) << "  " << ap.first; }
  LOG(DEBUG) << "Transform Passes";
  for (auto p : passMap) {
    if (analysisPasses.count(p.first) == 0) { LOG(DEBUG) << "  " << p.first; }
  }
}

PassManager::~PassManager() {
  for (auto p : passMap) { delete p.second; }
}

Pass::~Pass() {}
