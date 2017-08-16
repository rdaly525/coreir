#include "coreir.h"
#include "passes.h"

using namespace CoreIR;
Pass* Pass::getAnalysisBody(std::string ID) {
  assert(pm);
  ASSERT(std::find(dependencies.begin(),dependencies.end(),ID)!=dependencies.end(),ID + " not declared as a dependency for " + name);
  assert(pm->passMap.count(ID));
  return pm->passMap[ID];
}

Context* Pass::getContext() {
  assert(pm);
  return pm->c;
}
