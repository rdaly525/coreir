#include "coreir.h"
#include "coreir/passes/analysis/createfullinstancemap.h"

using namespace CoreIR;
using namespace std;

std::string Passes::CreateFullInstanceMap::ID = "createfullinstancemap";
bool Passes::CreateFullInstanceMap::runOnModule(Module* m) {
  for (auto instmap : m->getDef()->getInstances()) {
    Module* m = instmap.second->getModuleRef();
    if (m->generated()) {
      genInstanceMap[m->getGenerator()].insert(instmap.second);
    }
    else {
      modInstanceMap[m].insert(instmap.second);
    }
  }
  return false;
}
