#include "coreir.h"
#include "coreir/passes/transform/cullgraph.h"

using namespace std;
using namespace CoreIR;

namespace {
void recurse(Module* m, set<Module*>& mused, set<Generator*>& gused) {
  if (m->isGenerated()) {
    gused.insert(m->getGenerator());
  }
  else {
    mused.insert(m);
  }
  if (!m->hasDef()) return;
  for (auto ipair : m->getDef()->getInstances()) {
    recurse(ipair.second->getModuleRef(),mused,gused);
  }
}
}

string Passes::CullGraph::ID = "cullgraph";
bool Passes::CullGraph::runOnContext(Context* c) {
  if (!c->hasTop()) return false;
  //Find a list of all used Modules and Generators
  set<Module*> mused;
  set<Generator*> gused;
  recurse(c->getTop(),mused,gused);
  //if nocoreir, I need to keep all instances of any coreir definitions
  for (auto mpair : c->getNamespace("coreir")->getModules()) {
    recurse(mpair.second,mused,gused);
  }
  for (auto mpair : c->getNamespace("corebit")->getModules()) {
    recurse(mpair.second,mused,gused);
  }
  
  set<GlobalValue*> toErase;
  for (auto npair : c->getNamespaces()) {
    if (nocoreir && (npair.first=="coreir" || npair.first=="corebit")) {
      continue;
    }
    for (auto gpair : npair.second->getGenerators()) {
      if (gused.count(gpair.second)==0) {
        toErase.insert(gpair.second);
      }
    }
    for (auto mpair : npair.second->getModules()) {
      if (mused.count(mpair.second)==0 && !mpair.second->isGenerated()) {
        toErase.insert(mpair.second);
      }
    }
  }
  set<GlobalValue*> genToErase;
  for (auto i : toErase) {
    if (auto m = dyn_cast<Module>(i)) {
      m->getNamespace()->eraseModule(m->getName());
    }
    else {
      genToErase.insert(i);
    }
  }
  for (auto i : genToErase) {
    auto g = cast<Generator>(i);
    g->getNamespace()->eraseGenerator(g->getName());
  }
  return toErase.size()>0;
  
}
