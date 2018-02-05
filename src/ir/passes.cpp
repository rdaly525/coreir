#include "coreir/ir/passes.h"
#include "coreir/ir/passmanager.h"
#include "coreir/ir/module.h"
#include "coreir/ir/generator.h"

using namespace std;
using namespace CoreIR;

Pass* Pass::getAnalysisOutside(std::string ID) {
  return pm->getAnalysisPass(ID);
}
Context* Pass::getContext() {
  assert(pm);
  return pm->c;
}

bool InstanceVisitorPass::runOnModInstances(Module* m, set<Instance*>& instances) {
  if (modVisitorMap.count(m)==0) return false;
  auto fun = modVisitorMap[m];
  bool modified = false;
  for (auto inst : instances) {
    modified |= fun(inst);
  }
  return modified;
}

bool InstanceVisitorPass::runOnGenInstances(Generator* g, set<Instance*>& instances) {
  if (genVisitorMap.count(g)==0) return false;
  auto fun = genVisitorMap[g];
  bool modified = false;
  for (auto inst : instances) {
    modified |= fun(inst);
  }
  return modified;
}

void InstanceVisitorPass::addVisitorFunction(Module* m,InstanceVisitor_t fun) {
  ASSERT(!m->isGenerated(),"NYI visitor for generated module");
  ASSERT(modVisitorMap.count(m)==0,"Already added Function for " + m->getRefName());
  modVisitorMap[m] = fun;
}

void InstanceVisitorPass::addVisitorFunction(Generator* g,InstanceVisitor_t fun) {
  ASSERT(genVisitorMap.count(g)==0,"Already added Function for " + g->getRefName());
  genVisitorMap[g] = fun;
}
