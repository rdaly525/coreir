#include "coreir.h"
#include "passes.h"

using namespace CoreIR;

Pass* Pass::getAnalysisOutside(std::string ID) {
  return pm->getAnalysisPass(ID);
}
Context* Pass::getContext() {
  assert(pm);
  return pm->c;
}
