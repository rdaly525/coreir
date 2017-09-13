#include "coreir/ir/passes.h"
#include "coreir/ir/passmanager.h"
#include "coreir/ir/instantiable.hpp"

using namespace std;
using namespace CoreIR;

Pass* Pass::getAnalysisOutside(std::string ID) {
  return pm->getAnalysisPass(ID);
}
Context* Pass::getContext() {
  assert(pm);
  return pm->c;
}

bool InstanceVisitorPass::runOnInstances(Instantiable* i, unordered_set<Instance*>& instances) {
  if (visitorMap.count(i)==0) return false;
  auto fun = visitorMap[i];
  bool modified = false;
  for (auto inst : instances) {
    modified |= fun(inst);
  }
  return modified;
}


void InstanceVisitorPass::addVisitorFunction(Instantiable* i,InstanceVisitor_t fun) {
  ASSERT(visitorMap.count(i)==0,"Already added Function for " + i->getRefName());
  visitorMap[i] = fun;
}

