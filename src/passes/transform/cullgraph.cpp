#include "coreir.h"
#include "coreir/passes/transform/cullgraph.h"

using namespace std;
using namespace CoreIR;

namespace {
void recurse(Module* m, set<Module*>& mused, set<Generator*>& gused) {
  if (m->generated()) {
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
  set<Instantiable*> toErase;
  for (auto npair : c->getNamespaces()) {
    for (auto gpair : npair.second->getGenerators()) {
      if (gused.count(gpair.second)==0) {
        toErase.insert(gpair.second);
      }
    }
    for (auto mpair : npair.second->getModules()) {
      if (mused.count(mpair.second)==0 && !mpair.second->generated()) {
        toErase.insert(mpair.second);
      }
    }
  }
  for (auto i : toErase) {
    if (auto m = dyn_cast<Module>(i)) {
      m->getNamespace()->eraseModule(m->getName());
    }
  }
  for (auto i : toErase) {
    if (auto g = dyn_cast<Generator>(i)) {
      g->getNamespace()->eraseGenerator(g->getName());
    }
  }
  return toErase.size()>0;
  
}
