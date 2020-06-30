#include "coreir/passes/analysis/createinstancemap.h"
#include "coreir.h"

using namespace CoreIR;
using namespace std;

bool Passes::CreateInstanceMap::runOnModule(Module* m) {
  for (auto instmap : m->getDef()->getInstances()) {
    Module* m = instmap.second->getModuleRef();
    if (m->isGenerated()) {
      genInstanceMap[m->getGenerator()].insert(instmap.second);
    }
    else {
      modInstanceMap[m].insert(instmap.second);
    }
  }
  return false;
}
