#include "coreir.h"
#include "coreir/passes/transform/cullgraph.h"

using namespace std;
using namespace CoreIR;

namespace {
void recurse(Module* m, set<Instantiable*>& used) {
  used.insert(m);
  if (m->generated()) used.insert(m->getGenerator());
  if (!m->hasDef()) return;
  for (auto ipair : m->getDef()->getInstances()) {
    recurse(ipair.second->getModuleRef(),used);
  }
}
}

string Passes::CullGraph::ID = "cullgraph";
bool Passes::CullGraph::runOnContext(Context* c) {
  if (!c->hasTop()) return false;
  //Find a list of all used Modules and Generators
  set<Instantiable*> used;
  recurse(c->getTop(),used);
  
  set<Instantiable*> toErase;
  for (auto npair : c->getNamespaces()) {
    for (auto gpair : npair.second->getGenerators()) {
      if (used.count(gpair.second)==0) {
        toErase.insert(gpair.second);
      }
    }
    for (auto mpair : npair.second->getModules()) {
      if (used.count(mpair.second)==0) {
        toErase.insert(mpair.second);
      }
    }
  }
  //TODO really hacky fix
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
