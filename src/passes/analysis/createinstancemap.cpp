#include "coreir.h"
#include "coreir-passes/analysis/createinstancemap.h"

using namespace CoreIR;

std::string Passes::CreateInstanceMap::ID = "createinstancemap";
bool Passes::CreateInstanceMap::runOnModule(Module* m) {
  InstanceMapType imap;
  if (m->hasDef()) {
    ModuleDef* def = m->getDef();
    for (auto instmap : def->getInstances()) {
      Instantiable* i = instmap.second->getInstantiableRef();
      imap[i].insert(instmap.second);
    }
  }
  modInstanceMap[m] = imap;
  return false;
}
