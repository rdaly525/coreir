#include "passes/analysis/createinstancemap.h"
#include "ir/coreir.h"

using namespace CoreIR;
using namespace std;

std::string Passes::CreateInstanceMap::ID = "createfullinstancemap";
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
