#include "coreir/ir/passes.h"
#include "coreir/ir/passmanager.h"
#include "coreir/ir/instantiable.h"

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
  auto fun = modVisitorMap[g];
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
  ASSERT(visitorMap.count(i)==0,"Already added Function for " + i->getRefName());
  visitorMap[i] = fun;
}

void InstanceVisitorPass::addVisitorFunction(Generator* m,InstanceVisitor_t fun) {
  ASSERT(visitorMap.count(i)==0,"Already added Function for " + i->getRefName());
  visitorMap[i] = fun;
}
