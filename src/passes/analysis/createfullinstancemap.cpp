#include "coreir.h"
#include "coreir-passes/analysis/createfullinstancemap.h"

using namespace CoreIR;

std::string Passes::CreateFullInstanceMap::ID = "createfullinstancemap";
bool Passes::CreateFullInstanceMap::runOnModule(Module* m) {
  for (auto instmap : m->getDef()->getInstances()) {
    Instantiable* i = instmap.second->getInstantiableRef();
    instanceMap[i].insert(instmap.second);
  }
  return false;
}
